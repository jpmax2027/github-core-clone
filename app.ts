// github-core-clone-01 entry: a GitHub-compatible forge (REST v3, GraphQL v4, MCP, git smart-HTTP)
// in one file, Node standard library only. main.ts owns the lifecycle; this file is the server.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash, randomUUID } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const VIEWER = { id: 1000, login: 'adaiversen', name: 'ada iversen', email: 'adaiversen@example.invalid' };
const ZERO = '0'.repeat(40);
const VERSION = 'forge-1.0.0';

// --------------------------------------------------------------------------- git object store

type ObjType = 'blob' | 'tree' | 'commit' | 'tag';
interface Obj { type: ObjType; data: Buffer }

const objects = new Map<string, Obj>();

function hashObject(type: ObjType, data: Buffer): string {
  const head = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(head).update(data).digest('hex');
}
function storeObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objects.has(oid)) objects.set(oid, { type, data });
  return oid;
}
function getObject(oid: string): Obj | undefined { return objects.get(oid); }

interface TreeEntry { mode: string; name: string; oid: string }

function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    const mode = data.subarray(i, sp).toString('ascii');
    const nul = data.indexOf(0x00, sp);
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    out.push({ mode, name, oid });
    i = nul + 21;
  }
  return out;
}
/** Trees are immutable and content-addressed, so a parsed tree never goes stale. */
const parsedTrees = new Map<string, TreeEntry[]>();
function treeEntries(oid: string, data: Buffer): TreeEntry[] {
  let entries = parsedTrees.get(oid);
  if (!entries) { entries = parseTree(data); parsedTrees.set(oid, entries); }
  return entries;
}
function buildTreeData(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

/** Flatten a tree into path -> {mode, oid}; empty map for a missing tree. */
function flattenTree(treeOid: string | null, prefix = '', out = new Map<string, { mode: string; oid: string }>()): Map<string, { mode: string; oid: string }> {
  if (!treeOid) return out;
  const obj = getObject(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of treeEntries(treeOid, obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flattenTree(e.oid, path, out);
    else out.set(path, { mode: e.mode, oid: e.oid });
  }
  return out;
}
/** Build (and store) nested trees from a flat path map; returns the root tree oid. */
function buildTreeFromFlat(flat: Map<string, { mode: string; oid: string }>): string {
  interface Node { files: Map<string, { mode: string; oid: string }>; dirs: Map<string, Node> }
  const root: Node = { files: new Map(), dirs: new Map() };
  for (const [path, v] of flat) {
    const parts = path.split('/');
    let node = root;
    for (let i = 0; i < parts.length - 1; i++) {
      let next = node.dirs.get(parts[i]);
      if (!next) { next = { files: new Map(), dirs: new Map() }; node.dirs.set(parts[i], next); }
      node = next;
    }
    node.files.set(parts[parts.length - 1], v);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, v] of node.files) entries.push({ mode: v.mode, name, oid: v.oid });
    for (const [name, sub] of node.dirs) entries.push({ mode: '40000', name, oid: build(sub) });
    return storeObject('tree', buildTreeData(entries));
  };
  return build(root);
}

interface CommitInfo { tree: string; parents: string[]; message: string; ts: number; author: string }
function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split >= 0 ? text.slice(0, split) : text;
  const message = split >= 0 ? text.slice(split + 2) : '';
  let tree = ''; const parents: string[] = []; let ts = 0; let author = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) {
      author = line.slice(7);
      const m = / (\d+) [+-]\d{4}$/.exec(author);
      if (m) ts = Number(m[1]);
    }
  }
  return { tree, parents, message, ts, author };
}
let commitClock = Math.floor(Date.now() / 1000);
function nextTs(): number { commitClock = Math.max(commitClock + 1, Math.floor(Date.now() / 1000)); return commitClock; }
function makeCommit(tree: string, parents: string[], message: string, ts?: number): string {
  const when = ts ?? nextTs();
  const ident = `${VIEWER.name} <${VIEWER.email}> ${when} +0000`;
  const lines = [`tree ${tree}`, ...parents.map((p) => `parent ${p}`), `author ${ident}`, `committer ${ident}`];
  return storeObject('commit', Buffer.from(`${lines.join('\n')}\n\n${message}`, 'utf8'));
}
/** Commits are immutable and content-addressed, so a parsed commit never goes stale. */
const commitInfoCache = new Map<string, CommitInfo>();
function commitOf(oid: string): CommitInfo | null {
  const cached = commitInfoCache.get(oid);
  if (cached) return cached;
  const o = getObject(oid);
  if (!o || o.type !== 'commit') return null;
  const info = parseCommit(o.data);
  commitInfoCache.set(oid, info);
  return info;
}
/** All commits reachable from tips, newest first (BFS by generation, then timestamp desc). */
function reachableCommits(tips: string[], exclude = new Set<string>()): string[] {
  const seen = new Set<string>();
  const order: string[] = [];
  let frontier = tips.filter((t) => getObject(t)?.type === 'commit');
  while (frontier.length) {
    const next: string[] = [];
    for (const oid of frontier) {
      if (seen.has(oid) || exclude.has(oid)) continue;
      seen.add(oid); order.push(oid);
      const c = commitOf(oid);
      if (c) next.push(...c.parents);
    }
    frontier = next;
  }
  return order;
}
function isAncestor(anc: string, desc: string): boolean {
  return reachableCommits([desc]).includes(anc);
}
function mergeBase(a: string, b: string): string | null {
  const fromA = new Set(reachableCommits([a]));
  for (const oid of reachableCommits([b])) if (fromA.has(oid)) return oid;
  return null;
}

// --------------------------------------------------------------------------- packfiles

const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function packHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let rest = size;
  let first = (code << 4) | (rest & 0x0f);
  rest = Math.floor(rest / 16);
  while (rest > 0) { bytes.push(first | 0x80); first = rest & 0x7f; rest = Math.floor(rest / 128); }
  bytes.push(first);
  return Buffer.from(bytes);
}
function writePack(list: Obj[]): Buffer {
  const parts: Buffer[] = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 'ascii'); head.writeUInt32BE(2, 4); head.writeUInt32BE(list.length, 8);
  parts.push(head);
  for (const o of list) { parts.push(packHeader(o.type, o.data.length)); parts.push(deflateSync(o.data)); }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readSize = (): number => {
    let v = 0; let shift = 0;
    for (;;) { const b = delta[off++]; v += (b & 0x7f) * 2 ** shift; shift += 7; if (!(b & 0x80)) break; }
    return v;
  };
  const srcSize = readSize(); const tgtSize = readSize();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.alloc(tgtSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let cpOff = 0; let cpSize = 0; let shift = 0;
      for (let bit = 0; bit < 4; bit++) { if (op & (1 << bit)) cpOff += delta[off++] * 2 ** shift; shift += 8; }
      shift = 0;
      for (let bit = 4; bit < 7; bit++) { if (op & (1 << bit)) cpSize += delta[off++] * 2 ** shift; shift += 8; }
      if (cpSize === 0) cpSize = 0x10000;
      base.copy(out, written, cpOff, cpOff + cpSize);
      written += cpSize;
    } else if (op !== 0) {
      const n = op & 0x7f;
      delta.copy(out, written, off, off + n);
      off += n; written += n;
    } else throw new Error('delta opcode 0');
  }
  if (written !== tgtSize) throw new Error('delta size mismatch');
  return out;
}
/** Parse a pack into the store; returns the object ids it carried. Throws on corruption. */
function readPackIntoStore(pack: Buffer): string[] {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const trailer = pack.subarray(trailerStart).toString('hex');
  const computed = createHash('sha1').update(pack.subarray(0, trailerStart)).digest('hex');
  if (trailer !== computed) throw new Error('pack checksum mismatch');
  interface Raw { offset: number; typeCode: number; data: Buffer; baseOffset?: number; baseOid?: string }
  const raw: Raw[] = [];
  const byOffset = new Map<number, Raw>();
  let off = 12;
  for (let i = 0; i < count; i++) {
    const start = off;
    let b = pack[off];
    const first = b;
    let size = b & 0x0f; let shift = 4; off += 1;
    while (b & 0x80) { b = pack[off++]; size += (b & 0x7f) * 2 ** shift; shift += 7; }
    const typeCode = (first >> 4) & 0x07;
    const entry: Raw = { offset: start, typeCode, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      let byte = pack[off++]; let value = byte & 0x7f;
      while (byte & 0x80) { byte = pack[off++]; value = ((value + 1) * 128) + (byte & 0x7f); }
      entry.baseOffset = start - value;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(off, off + 20).toString('hex'); off += 20;
    }
    const inflated = inflateSync(pack.subarray(off, trailerStart), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    if (inflated.buffer.length !== size) throw new Error('pack entry size mismatch');
    entry.data = inflated.buffer;
    off += inflated.engine.bytesWritten;
    raw.push(entry); byOffset.set(start, entry);
  }
  const ids: string[] = [];
  const resolve = (e: Raw, seen: Set<number>): { type: ObjType; data: Buffer } => {
    if (seen.has(e.offset)) throw new Error('delta cycle');
    seen.add(e.offset);
    if (e.typeCode === 6) {
      const baseEntry = byOffset.get(e.baseOffset!);
      if (!baseEntry) throw new Error('ofs base missing');
      const base = resolve(baseEntry, seen);
      return { type: base.type, data: applyDelta(base.data, e.data) };
    }
    if (e.typeCode === 7) {
      let base: { type: ObjType; data: Buffer } | undefined;
      const inPack = raw.find((r) => r.typeCode !== 6 && r.typeCode !== 7 && hashObject(CODE_TYPE[r.typeCode], r.data) === e.baseOid);
      if (inPack) base = { type: CODE_TYPE[inPack.typeCode], data: inPack.data };
      else {
        const stored = getObject(e.baseOid!);
        if (stored) base = stored;
        else {
          const deltaBase = raw.find((r) => (r.typeCode === 6 || r.typeCode === 7));
          if (deltaBase) { const r = resolve(deltaBase, new Set()); if (hashObject(r.type, r.data) === e.baseOid) base = r; }
        }
      }
      if (!base) throw new Error('ref base missing');
      return { type: base.type, data: applyDelta(base.data, e.data) };
    }
    return { type: CODE_TYPE[e.typeCode], data: e.data };
  };
  for (const e of raw) {
    const r = resolve(e, new Set());
    ids.push(storeObject(r.type, r.data));
  }
  return ids;
}

// --------------------------------------------------------------------------- pkt-line

function pkt(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = data.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
function parsePktLines(buf: Buffer, start = 0): { lines: Buffer[]; rest: number } {
  const lines: Buffer[] = [];
  let off = start;
  while (off + 4 <= buf.length) {
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error('bad pkt-line');
    const len = parseInt(hex, 16);
    if (len === 0) { off += 4; return { lines, rest: off }; }
    if (len < 4 || off + len > buf.length) throw new Error('pkt-line overrun');
    lines.push(buf.subarray(off + 4, off + len));
    off += len;
  }
  return { lines, rest: off };
}

// --------------------------------------------------------------------------- forge store

interface Label { id: number; name: string; color: string; description: string }
interface Comment { id: number; body: string; user: string; created: number; issueNumber: number }
interface Issue {
  kind: 'issue' | 'pull';
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: string[]; created: number; seq: number;
  // pull-only
  headRef?: string; baseRef?: string; merged?: boolean; mergedAt?: string | null; mergeCommitSha?: string | null;
}
interface Repo {
  id: number; owner: string; name: string; description: string; priv: boolean; defaultBranch: string;
  refs: Map<string, string>; labels: Map<string, Label>; items: Issue[]; comments: Comment[];
  nextNumber: number; created: number;
}

const repos = new Map<string, Repo>();
let nextRepoId = 1;
let nextLabelId = 1;
let nextCommentId = 1;
let nextIssueId = 1;
let seqCounter = 0;

const repoKey = (owner: string, name: string): string => `${owner}/${name}`;
function findRepo(owner: string, name: string): Repo | undefined { return repos.get(repoKey(owner, name)); }
function createRepo(owner: string, name: string, description: string, priv: boolean): Repo {
  const repo: Repo = {
    id: nextRepoId++, owner, name, description, priv, defaultBranch: 'main',
    refs: new Map(), labels: new Map(), items: [], comments: [], nextNumber: 1, created: Date.now(),
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}
function repoJson(r: Repo): Record<string, unknown> {
  return {
    id: r.id, name: r.name, full_name: repoKey(r.owner, r.name),
    owner: { login: r.owner, id: r.owner === VIEWER.login ? VIEWER.id : 0 },
    private: r.priv, description: r.description, default_branch: r.defaultBranch,
    html_url: `/${r.owner}/${r.name}`, created_at: new Date(r.created).toISOString(),
  };
}
function labelJson(l: Label): Record<string, unknown> {
  return { id: l.id, name: l.name, color: l.color, description: l.description };
}
function issueJson(r: Repo, i: Issue): Record<string, unknown> {
  const iso = new Date(i.created).toISOString();
  return {
    id: i.id, number: i.number, title: i.title, body: i.body, state: i.state,
    labels: i.labels.map((n) => { const l = r.labels.get(n); return l ? labelJson(l) : { name: n }; }),
    user: { login: VIEWER.login, id: VIEWER.id },
    comments: r.comments.filter((c) => c.issueNumber === i.number).length,
    created_at: iso, updated_at: iso,
  };
}
function pullJson(r: Repo, i: Issue): Record<string, unknown> {
  const headSha = r.refs.get(`refs/heads/${i.headRef}`) ?? ZERO;
  const baseSha = r.refs.get(`refs/heads/${i.baseRef}`) ?? ZERO;
  return {
    ...issueJson(r, i),
    state: i.state, merged: i.merged === true, merged_at: i.mergedAt ?? null,
    merge_commit_sha: i.mergeCommitSha ?? null,
    head: { ref: i.headRef, sha: headSha, label: `${r.owner}:${i.headRef}` },
    base: { ref: i.baseRef, sha: baseSha, label: `${r.owner}:${i.baseRef}` },
  };
}
function commentJson(c: Comment): Record<string, unknown> {
  const iso = new Date(c.created).toISOString();
  return { id: c.id, body: c.body, user: { login: c.user, id: VIEWER.id }, created_at: iso, updated_at: iso };
}

// --- branch / tree helpers over the store

function branchTip(r: Repo, branch: string): string | null {
  return r.refs.get(`refs/heads/${branch}`) ?? null;
}
function refTip(r: Repo, ref: string): string | null {
  if (r.refs.has(ref)) return r.refs.get(ref)!;
  if (r.refs.has(`refs/heads/${ref}`)) return r.refs.get(`refs/heads/${ref}`)!;
  if (/^[0-9a-f]{40}$/.test(ref) && getObject(ref)?.type === 'commit') return ref;
  return null;
}
function flatAt(r: Repo, ref: string): Map<string, { mode: string; oid: string }> {
  const tip = refTip(r, ref);
  if (!tip) return new Map();
  const c = commitOf(tip);
  return c ? flattenTree(c.tree) : new Map();
}
/** Commit a new flat tree onto a branch; returns the commit oid. */
function commitFlat(r: Repo, branch: string, flat: Map<string, { mode: string; oid: string }>, message: string): string {
  const tree = buildTreeFromFlat(flat);
  const parent = branchTip(r, branch);
  const oid = makeCommit(tree, parent ? [parent] : [], message);
  r.refs.set(`refs/heads/${branch}`, oid);
  return oid;
}

// --- line diff (LCS) for pull files

function lineDiff(a: string, b: string): { additions: number; deletions: number } {
  const al = a === '' ? [] : a.split('\n');
  const bl = b === '' ? [] : b.split('\n');
  const n = al.length; const m = bl.length;
  const dp: number[] = new Array((n + 1) * (m + 1)).fill(0);
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i * (m + 1) + j] = al[i] === bl[j] ? dp[(i + 1) * (m + 1) + j + 1] + 1 : Math.max(dp[(i + 1) * (m + 1) + j], dp[i * (m + 1) + j + 1]);
    }
  }
  const common = dp[0];
  return { additions: m - common, deletions: n - common };
}
interface FileChange { filename: string; status: string; additions: number; deletions: number; changes: number }
function pullFiles(r: Repo, i: Issue): FileChange[] {
  const baseFlat = flatAt(r, i.baseRef!);
  const headFlat = flatAt(r, i.headRef!);
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  const out: FileChange[] = [];
  for (const p of [...paths].sort()) {
    const b = baseFlat.get(p); const h = headFlat.get(p);
    if (b && h && b.oid === h.oid) continue;
    const bText = b ? (getObject(b.oid)?.data.toString('utf8') ?? '') : '';
    const hText = h ? (getObject(h.oid)?.data.toString('utf8') ?? '') : '';
    const d = lineDiff(bText, hText);
    out.push({
      filename: p,
      status: !b ? 'added' : !h ? 'removed' : 'modified',
      additions: d.additions, deletions: d.deletions, changes: d.additions + d.deletions,
    });
  }
  return out;
}
/** 3-way merge of head into base; returns merged flat map or null on conflict. */
function tryMerge(r: Repo, i: Issue): Map<string, { mode: string; oid: string }> | null {
  const baseTip = branchTip(r, i.baseRef!);
  const headTip = branchTip(r, i.headRef!);
  if (!baseTip || !headTip) return null;
  const mb = mergeBase(baseTip, headTip);
  const baseFlat = mb ? flattenTree(commitOf(mb)?.tree ?? null) : new Map<string, { mode: string; oid: string }>();
  const ours = flatAt(r, i.baseRef!);
  const theirs = flatAt(r, i.headRef!);
  const paths = new Set([...baseFlat.keys(), ...ours.keys(), ...theirs.keys()]);
  const merged = new Map<string, { mode: string; oid: string }>();
  for (const p of paths) {
    const b = baseFlat.get(p); const o = ours.get(p); const t = theirs.get(p);
    const same = (x?: { oid: string }, y?: { oid: string }): boolean => (x?.oid ?? null) === (y?.oid ?? null);
    let pick: { mode: string; oid: string } | undefined;
    if (same(o, t)) pick = o;
    else if (same(b, o)) pick = t;
    else if (same(b, t)) pick = o;
    else return null;
    if (pick) merged.set(p, pick);
  }
  return merged;
}
function mergePull(r: Repo, i: Issue): { sha: string } | 'conflict' | 'gone' {
  if (i.state === 'closed' && i.merged) return { sha: i.mergeCommitSha ?? ZERO };
  const baseTip = branchTip(r, i.baseRef!);
  const headTip = branchTip(r, i.headRef!);
  if (!baseTip || !headTip) return 'gone';
  if (isAncestor(headTip, baseTip)) {
    i.state = 'closed'; i.merged = true; i.mergedAt = new Date().toISOString(); i.mergeCommitSha = baseTip;
    return { sha: baseTip };
  }
  const merged = tryMerge(r, i);
  if (!merged) return 'conflict';
  const tree = buildTreeFromFlat(merged);
  const sha = makeCommit(tree, [baseTip], `${i.title}\n\n${i.body}\n`);
  r.refs.set(`refs/heads/${i.baseRef}`, sha);
  i.state = 'closed'; i.merged = true; i.mergedAt = new Date().toISOString(); i.mergeCommitSha = sha;
  return { sha };
}

// --- global ids for GraphQL

function gid(kind: string, ...parts: (string | number)[]): string {
  return Buffer.from(`${kind}:${parts.join(':')}`, 'utf8').toString('base64');
}
function parseGid(id: string): string[] | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const parts = text.split(':');
    return parts.length >= 2 ? parts : null;
  } catch { return null; }
}
function repoByDbId(id: number): Repo | undefined {
  for (const r of repos.values()) if (r.id === id) return r;
  return undefined;
}

// --------------------------------------------------------------------------- HTTP plumbing

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const text = body === undefined ? '' : `${JSON.stringify(body)}\n`;
  const buf = text ? Buffer.from(text, 'utf8') : null;
  res.writeHead(status, {
    'content-type': JSON_TYPE, 'x-github-request-id': randomUUID(),
    ...(buf ? { 'content-length': buf.length } : {}), ...headers,
  });
  res.end(buf ?? '');
}
function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length, 'x-github-request-id': randomUUID() });
  res.end(body);
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function authed(req: IncomingMessage): boolean {
  if (!TOKEN) return true;
  return req.headers.authorization === `Bearer ${TOKEN}`;
}
function paginate<T>(res: ServerResponse, req: IncomingMessage, url: URL, items: T[]): T[] {
  const perPage = Math.min(100, Math.max(1, Number(url.searchParams.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(url.searchParams.get('page') ?? '1') || 1);
  const totalPages = Math.ceil(items.length / perPage);
  if (page < totalPages) {
    const host = req.headers.host ?? 'entry';
    const next = new URL(url.pathname, `http://${host}`);
    for (const [k, v] of url.searchParams) if (k !== 'page') next.searchParams.set(k, v);
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    const last = new URL(url.pathname, `http://${host}`);
    for (const [k, v] of url.searchParams) if (k !== 'page') last.searchParams.set(k, v);
    last.searchParams.set('per_page', String(perPage));
    last.searchParams.set('page', String(totalPages));
    res.setHeader('link', `<${next.toString()}>; rel="next", <${last.toString()}>; rel="last"`);
  }
  return items.slice((page - 1) * perPage, page * perPage);
}

// --------------------------------------------------------------------------- REST v3

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL, seg: string[]): Promise<void> {
  const method = req.method ?? 'GET';
  const raw = await readBody(req);
  let body: Record<string, unknown> = {};
  if (raw.length > 0 && (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE')) {
    try { body = JSON.parse(raw.toString('utf8')) as Record<string, unknown>; }
    catch { sendJson(res, 400, { message: 'Problems parsing JSON' }); return; }
  }
  const notFound = (): void => { sendJson(res, 404, { message: 'Not Found' }); };

  // root + meta (root mirrors the starter: no auth gate)
  if (seg.length === 0) {
    if (method === 'GET') { sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' }); return; }
    notFound(); return;
  }
  if (!authed(req)) { sendJson(res, 401, { message: 'Bad credentials' }); return; }
  if (seg[0] === 'meta' && seg.length === 1) {
    if (method === 'GET') { sendJson(res, 200, { installed_version: VERSION, verifiable_password_authentication: false }); return; }
    notFound(); return;
  }
  if (seg[0] === 'user' && seg.length === 1) {
    if (method === 'GET') { sendJson(res, 200, { login: VIEWER.login, id: VIEWER.id, name: VIEWER.name, email: VIEWER.email, type: 'User' }); return; }
    notFound(); return;
  }
  if (seg[0] === 'user' && seg[1] === 'repos' && seg.length === 2) {
    if (method === 'GET') {
      const mine = [...repos.values()].filter((r) => r.owner === VIEWER.login).sort((a, b) => a.id - b.id);
      sendJson(res, 200, paginate(res, req, url, mine).map(repoJson)); return;
    }
    if (method === 'POST') {
      const name = String(body.name ?? '');
      if (!name) { sendJson(res, 422, { message: 'Validation Failed: name is required' }); return; }
      if (findRepo(VIEWER.login, name)) { sendJson(res, 422, { message: 'Validation Failed: name already exists on this account' }); return; }
      const repo = createRepo(VIEWER.login, name, String(body.description ?? ''), body.private === true);
      if (body.auto_init === true) {
        const blob = storeObject('blob', Buffer.from(`# ${name}\n`, 'utf8'));
        commitFlat(repo, repo.defaultBranch, new Map([['README.md', { mode: '100644', oid: blob }]]), 'Initial commit');
      }
      sendJson(res, 201, repoJson(repo)); return;
    }
    notFound(); return;
  }
  if (seg[0] !== 'repos' || seg.length < 3) { notFound(); return; }
  const owner = seg[1]; const name = seg[2];
  const repo = findRepo(owner, name);
  if (!repo) { notFound(); return; }
  const rest = seg.slice(3);

  if (rest.length === 0) {
    if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return; }
    if (method === 'PATCH') {
      if (typeof body.description === 'string') repo.description = body.description;
      if (typeof body.private === 'boolean') repo.priv = body.private;
      if (typeof body.name === 'string' && body.name && body.name !== repo.name && !findRepo(owner, body.name)) {
        repos.delete(repoKey(owner, repo.name)); repo.name = body.name; repos.set(repoKey(owner, repo.name), repo);
      }
      if (typeof body.default_branch === 'string' && body.default_branch) repo.defaultBranch = body.default_branch;
      sendJson(res, 200, repoJson(repo)); return;
    }
    if (method === 'DELETE') { repos.delete(repoKey(owner, name)); sendJson(res, 204, undefined); return; }
    notFound(); return;
  }

  // branches
  if (rest[0] === 'branches') {
    if (rest.length === 1 && method === 'GET') {
      const out = [...repo.refs.entries()].filter(([r]) => r.startsWith('refs/heads/'))
        .map(([r, sha]) => ({ name: r.slice('refs/heads/'.length), commit: { sha }, protected: false }));
      sendJson(res, 200, out); return;
    }
    if (rest.length === 2 && method === 'GET') {
      const branch = decodeURIComponent(rest[1]);
      const tip = branchTip(repo, branch);
      if (!tip) { notFound(); return; }
      sendJson(res, 200, { name: branch, commit: { sha: tip }, protected: false }); return;
    }
    notFound(); return;
  }

  // git refs
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (rest.length === 2 && method === 'POST') {
      const ref = String(body.ref ?? ''); const sha = String(body.sha ?? '');
      if (!ref.startsWith('refs/') || !getObject(sha)) { sendJson(res, 422, { message: 'Validation Failed' }); return; }
      repo.refs.set(ref, sha);
      sendJson(res, 201, { ref, node_id: gid('REF', repo.id, ref), url: '', object: { sha, type: getObject(sha)!.type, url: '' } }); return;
    }
    if (rest.length >= 3 && method === 'GET') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (!sha) { notFound(); return; }
      sendJson(res, 200, { ref, node_id: gid('REF', repo.id, ref), url: '', object: { sha, type: getObject(sha)?.type ?? 'commit', url: '' } }); return;
    }
    if (rest.length >= 3 && method === 'DELETE') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      if (!repo.refs.delete(ref)) { notFound(); return; }
      sendJson(res, 204, undefined); return;
    }
    notFound(); return;
  }

  // commits
  if (rest[0] === 'commits') {
    if (rest.length === 1 && method === 'GET') {
      const ref = url.searchParams.get('sha') ?? repo.defaultBranch;
      const tip = refTip(repo, ref);
      if (!tip) { sendJson(res, 200, []); return; }
      const list = reachableCommits([tip]).map((oid) => {
        const c = commitOf(oid)!;
        return { sha: oid, commit: { message: c.message, author: { name: VIEWER.name, email: VIEWER.email, date: new Date(c.ts * 1000).toISOString() }, tree: { sha: c.tree } }, parents: c.parents.map((p) => ({ sha: p })) };
      });
      sendJson(res, 200, paginate(res, req, url, list)); return;
    }
    if (rest.length === 2 && method === 'GET') {
      const c = commitOf(rest[1]);
      if (!c) { notFound(); return; }
      sendJson(res, 200, { sha: rest[1], commit: { message: c.message, author: { name: VIEWER.name, email: VIEWER.email, date: new Date(c.ts * 1000).toISOString() }, tree: { sha: c.tree } }, parents: c.parents.map((p) => ({ sha: p })) }); return;
    }
    notFound(); return;
  }

  // contents
  if (rest[0] === 'contents') {
    const path = rest.slice(1).map(decodeURIComponent).join('/');
    if (method === 'GET') {
      const ref = url.searchParams.get('ref') ?? repo.defaultBranch;
      const flat = flatAt(repo, ref);
      const file = flat.get(path);
      if (file) {
        const data = getObject(file.oid)!.data;
        sendJson(res, 200, { type: 'file', encoding: 'base64', name: path.split('/').pop(), path, sha: file.oid, size: data.length, content: data.toString('base64') });
        return;
      }
      const prefix = path === '' ? '' : `${path}/`;
      const entries = new Map<string, { type: string; sha: string }>();
      for (const [p, v] of flat) {
        if (!p.startsWith(prefix)) continue;
        const tail = p.slice(prefix.length);
        const slash = tail.indexOf('/');
        if (slash < 0) entries.set(tail, { type: 'file', sha: v.oid });
        else if (!entries.has(tail.slice(0, slash))) entries.set(tail.slice(0, slash), { type: 'dir', sha: '' });
      }
      if (entries.size === 0 && path !== '') { notFound(); return; }
      const out = [...entries.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([n, v]) => ({
        type: v.type, name: n, path: prefix + n, sha: v.sha || buildTreeFromFlat(new Map([...flat].filter(([p]) => p.startsWith(`${prefix}${n}/`)))),
      }));
      sendJson(res, 200, out); return;
    }
    if (method === 'PUT') {
      const branch = String(body.branch ?? repo.defaultBranch);
      const flat = flatAt(repo, branch);
      const existing = flat.get(path);
      if (existing && !body.sha) { sendJson(res, 422, { message: 'Validation Failed: sha is required when updating' }); return; }
      if (existing && body.sha !== existing.oid) { sendJson(res, 409, { message: `${path} has changed since the given sha` }); return; }
      if (!existing && body.sha) { sendJson(res, 422, { message: 'Validation Failed: sha given for a new file' }); return; }
      const data = Buffer.from(String(body.content ?? ''), 'base64');
      const blob = storeObject('blob', data);
      flat.set(path, { mode: '100644', oid: blob });
      const commit = commitFlat(repo, branch, flat, String(body.message ?? `Update ${path}`));
      sendJson(res, existing ? 200 : 201, {
        content: { type: 'file', name: path.split('/').pop(), path, sha: blob, size: data.length, encoding: 'base64' },
        commit: { sha: commit, message: String(body.message ?? '') },
      });
      return;
    }
    if (method === 'DELETE') {
      const branch = String(body.branch ?? repo.defaultBranch);
      const flat = flatAt(repo, branch);
      const existing = flat.get(path);
      if (!existing) { notFound(); return; }
      if (body.sha && body.sha !== existing.oid) { sendJson(res, 409, { message: `${path} has changed since the given sha` }); return; }
      flat.delete(path);
      const commit = commitFlat(repo, branch, flat, String(body.message ?? `Delete ${path}`));
      sendJson(res, 200, { content: null, commit: { sha: commit, message: String(body.message ?? '') } }); return;
    }
    notFound(); return;
  }

  // labels
  if (rest[0] === 'labels') {
    if (rest.length === 1 && method === 'GET') { sendJson(res, 200, [...repo.labels.values()].map(labelJson)); return; }
    if (rest.length === 1 && method === 'POST') {
      const lname = String(body.name ?? '');
      if (!lname) { sendJson(res, 422, { message: 'Validation Failed: name is required' }); return; }
      if (repo.labels.has(lname)) { sendJson(res, 422, { message: 'Validation Failed: label already exists' }); return; }
      const label: Label = { id: nextLabelId++, name: lname, color: String(body.color ?? 'ededed').replace(/^#/, ''), description: String(body.description ?? '') };
      repo.labels.set(lname, label);
      sendJson(res, 201, labelJson(label)); return;
    }
    notFound(); return;
  }

  // issues + comments
  if (rest[0] === 'issues') {
    if (rest.length === 1 && method === 'GET') {
      let list = repo.items.filter((i) => i.kind === 'issue');
      const state = url.searchParams.get('state') ?? 'open';
      if (state !== 'all') list = list.filter((i) => i.state === state);
      const direction = url.searchParams.get('direction') ?? 'desc';
      list = [...list].sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
      sendJson(res, 200, paginate(res, req, url, list).map((i) => issueJson(repo, i))); return;
    }
    if (rest.length === 1 && method === 'POST') {
      const labelNames = Array.isArray(body.labels) ? body.labels.map(String) : [];
      for (const n of labelNames) if (!repo.labels.has(n)) { sendJson(res, 422, { message: `Validation Failed: label '${n}' does not exist` }); return; }
      const issue: Issue = {
        kind: 'issue', id: nextIssueId++, number: repo.nextNumber++, title: String(body.title ?? ''), body: String(body.body ?? ''),
        state: 'open', labels: labelNames, created: Date.now(), seq: seqCounter++,
      };
      repo.items.push(issue);
      sendJson(res, 201, issueJson(repo, issue)); return;
    }
    const num = Number(rest[1]);
    const issue = repo.items.find((i) => i.kind === 'issue' && i.number === num);
    if (rest.length === 2) {
      if (!issue) { notFound(); return; }
      if (method === 'GET') { sendJson(res, 200, issueJson(repo, issue)); return; }
      if (method === 'PATCH') {
        if (typeof body.title === 'string') issue.title = body.title;
        if (typeof body.body === 'string') issue.body = body.body;
        if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
        if (Array.isArray(body.labels)) {
          const names = body.labels.map(String);
          for (const n of names) if (!repo.labels.has(n)) { sendJson(res, 422, { message: `Validation Failed: label '${n}' does not exist` }); return; }
          issue.labels = names;
        }
        sendJson(res, 200, issueJson(repo, issue)); return;
      }
      notFound(); return;
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (!issue) { notFound(); return; }
      if (method === 'GET') {
        const list = repo.comments.filter((c) => c.issueNumber === num).sort((a, b) => a.id - b.id);
        sendJson(res, 200, paginate(res, req, url, list).map(commentJson)); return;
      }
      if (method === 'POST') {
        const comment: Comment = { id: nextCommentId++, body: String(body.body ?? ''), user: VIEWER.login, created: Date.now(), issueNumber: num };
        repo.comments.push(comment);
        sendJson(res, 201, commentJson(comment)); return;
      }
      notFound(); return;
    }
    notFound(); return;
  }

  // pulls
  if (rest[0] === 'pulls') {
    if (rest.length === 1 && method === 'GET') {
      let list = repo.items.filter((i) => i.kind === 'pull');
      const state = url.searchParams.get('state') ?? 'open';
      if (state !== 'all') list = list.filter((i) => i.state === state);
      const direction = url.searchParams.get('direction') ?? 'desc';
      list = [...list].sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
      sendJson(res, 200, paginate(res, req, url, list).map((i) => pullJson(repo, i))); return;
    }
    if (rest.length === 1 && method === 'POST') {
      const head = String(body.head ?? ''); const base = String(body.base ?? repo.defaultBranch);
      if (!head || !branchTip(repo, head) || !branchTip(repo, base)) { sendJson(res, 422, { message: 'Validation Failed: head or base branch does not exist' }); return; }
      const pull: Issue = {
        kind: 'pull', id: nextIssueId++, number: repo.nextNumber++, title: String(body.title ?? ''), body: String(body.body ?? ''),
        state: 'open', labels: [], created: Date.now(), seq: seqCounter++, headRef: head, baseRef: base,
        merged: false, mergedAt: null, mergeCommitSha: null,
      };
      repo.items.push(pull);
      sendJson(res, 201, pullJson(repo, pull)); return;
    }
    const num = Number(rest[1]);
    const pull = repo.items.find((i) => i.kind === 'pull' && i.number === num);
    if (rest.length === 2) {
      if (!pull) { notFound(); return; }
      if (method === 'GET') { sendJson(res, 200, pullJson(repo, pull)); return; }
      if (method === 'PATCH') {
        if (typeof body.title === 'string') pull.title = body.title;
        if (typeof body.body === 'string') pull.body = body.body;
        if (body.state === 'open' || body.state === 'closed') pull.state = body.state;
        sendJson(res, 200, pullJson(repo, pull)); return;
      }
      notFound(); return;
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      if (!pull) { notFound(); return; }
      sendJson(res, 200, paginate(res, req, url, pullFiles(repo, pull))); return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (!pull) { notFound(); return; }
      const result = mergePull(repo, pull);
      if (result === 'conflict') { sendJson(res, 405, { message: 'Pull Request is not mergeable' }); return; }
      if (result === 'gone') { sendJson(res, 405, { message: 'Pull Request is not mergeable' }); return; }
      sendJson(res, 200, { sha: result.sha, merged: true, message: 'Pull Request successfully merged' }); return;
    }
    notFound(); return;
  }

  notFound();
}

// --------------------------------------------------------------------------- MCP

const MCP_TOOLS = [
  {
    name: 'create_repo', description: 'Create a new repository for the authenticated user.',
    inputSchema: { type: 'object', properties: { name: { type: 'string' }, description: { type: 'string' }, private: { type: 'boolean' } }, required: ['name'] },
  },
  {
    name: 'get_repo', description: 'Get a repository by owner and name.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue', description: 'Create an issue in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues', description: 'List issues in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, state: { type: 'string' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request', description: 'Create a pull request in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, head: { type: 'string' }, base: { type: 'string' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request', description: 'Merge a pull request by number.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, pull_number: { type: 'number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
] as const;
const MCP_TOOLS_JSON = JSON.stringify(MCP_TOOLS);

function toolResult(obj: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj as Record<string, unknown> };
}
function toolError(text: string): Record<string, unknown> {
  return { content: [{ type: 'text', text }], isError: true };
}
function runTool(name: string, args: Record<string, unknown>): Record<string, unknown> | null {
  const need = (...keys: string[]): boolean => keys.every((k) => args[k] !== undefined && args[k] !== null && args[k] !== '');
  switch (name) {
    case 'create_repo': {
      if (!need('name')) return null;
      const rname = String(args.name);
      if (findRepo(VIEWER.login, rname)) return toolError(`repository ${VIEWER.login}/${rname} already exists`);
      const repo = createRepo(VIEWER.login, rname, String(args.description ?? ''), args.private === true);
      return toolResult(repoJson(repo));
    }
    case 'get_repo': {
      if (!need('owner', 'repo')) return null;
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return toolError(`repository ${String(args.owner)}/${String(args.repo)} not found`);
      return toolResult(repoJson(repo));
    }
    case 'create_issue': {
      if (!need('owner', 'repo', 'title')) return null;
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return toolError('repository not found');
      const issue: Issue = {
        kind: 'issue', id: nextIssueId++, number: repo.nextNumber++, title: String(args.title), body: String(args.body ?? ''),
        state: 'open', labels: [], created: Date.now(), seq: seqCounter++,
      };
      repo.items.push(issue);
      return toolResult(issueJson(repo, issue));
    }
    case 'list_issues': {
      if (!need('owner', 'repo')) return null;
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return toolError('repository not found');
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.items.filter((i) => i.kind === 'issue' && (state === 'all' || i.state === state))
        .sort((a, b) => a.seq - b.seq).map((i) => issueJson(repo, i));
      return toolResult({ issues: list, count: list.length });
    }
    case 'create_pull_request': {
      if (!need('owner', 'repo', 'title', 'head', 'base')) return null;
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return toolError('repository not found');
      const head = String(args.head); const base = String(args.base);
      if (!branchTip(repo, head) || !branchTip(repo, base)) return toolError('head or base branch does not exist');
      const pull: Issue = {
        kind: 'pull', id: nextIssueId++, number: repo.nextNumber++, title: String(args.title), body: String(args.body ?? ''),
        state: 'open', labels: [], created: Date.now(), seq: seqCounter++, headRef: head, baseRef: base,
        merged: false, mergedAt: null, mergeCommitSha: null,
      };
      repo.items.push(pull);
      return toolResult(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      if (!need('owner', 'repo', 'pull_number')) return null;
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return toolError('repository not found');
      const pull = repo.items.find((i) => i.kind === 'pull' && i.number === Number(args.pull_number));
      if (!pull) return toolError('pull request not found');
      const result = mergePull(repo, pull);
      if (result === 'conflict' || result === 'gone') return toolError('Pull Request is not mergeable');
      return toolResult({ ...pullJson(repo, pull), sha: result.sha, merged: true });
    }
    default: return undefined as unknown as null;
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const raw = await readBody(req);
  if (!authed(req)) { sendJson(res, 401, { jsonrpc: '2.0', id: null, error: { code: -32001, message: 'unauthorized' } }); return; }
  let parsed: unknown;
  try { parsed = JSON.parse(raw.toString('utf8')); }
  catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const handleOne = (msg: Record<string, unknown>): Record<string, unknown> | null => {
    const id = msg.id as string | number | undefined;
    const method = String(msg.method ?? '');
    const isNotification = id === undefined;
    if (method === 'server/discover') {
      return {
        jsonrpc: '2.0', id: id ?? null,
        result: {
          supportedVersions: ['2026-07-28', '2025-11-25'],
          capabilities: { tools: {} },
          serverInfo: { name: 'forge', version: VERSION },
          _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: VERSION } },
        },
      };
    }
    if (method === 'initialize') {
      const params = (msg.params ?? {}) as Record<string, unknown>;
      const offered = String(params.protocolVersion ?? '');
      const supported = ['2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05', '2026-07-28'];
      return {
        jsonrpc: '2.0', id: id ?? null,
        result: {
          protocolVersion: supported.includes(offered) ? offered : '2025-11-25',
          capabilities: { tools: {} },
          serverInfo: { name: 'forge', version: VERSION },
        },
      };
    }
    if (isNotification) return null;
    if (method === 'ping') return { jsonrpc: '2.0', id: id ?? null, result: {} };
    if (method === 'tools/list') return { jsonrpc: '2.0', id: id ?? null, result: { tools: JSON.parse(MCP_TOOLS_JSON) } };
    if (method === 'tools/call') {
      const params = (msg.params ?? {}) as Record<string, unknown>;
      const toolName = String(params.name ?? '');
      const args = (params.arguments ?? {}) as Record<string, unknown>;
      if (!MCP_TOOLS.some((t) => t.name === toolName)) {
        return { jsonrpc: '2.0', id: id ?? null, error: { code: -32602, message: `unknown tool: ${toolName}` } };
      }
      const result = runTool(toolName, args);
      if (result === null) return { jsonrpc: '2.0', id: id ?? null, error: { code: -32602, message: 'missing required arguments' } };
      return { jsonrpc: '2.0', id: id ?? null, result };
    }
    return { jsonrpc: '2.0', id: id ?? null, error: { code: -32601, message: `method not found: ${method}` } };
  };
  if (Array.isArray(parsed)) {
    const out: unknown[] = [];
    for (const msg of parsed) {
      const r = handleOne(msg as Record<string, unknown>);
      if (r) out.push(r);
    }
    sendJson(res, 200, out);
    return;
  }
  const msg = parsed as Record<string, unknown>;
  if (msg.id === undefined) { // notification
    res.writeHead(202, { 'x-github-request-id': randomUUID() });
    res.end();
    return;
  }
  const result = handleOne(msg);
  if (result === null) { res.writeHead(202, { 'x-github-request-id': randomUUID() }); res.end(); return; }
  sendJson(res, 200, result);
}

// --------------------------------------------------------------------------- GraphQL

type GValue =
  | { k: 'var'; v: string } | { k: 'str'; v: string } | { k: 'num'; v: number }
  | { k: 'bool'; v: boolean } | { k: 'null' } | { k: 'list'; v: GValue[] }
  | { k: 'obj'; v: Map<string, GValue> };
interface GField { name: string; alias: string | null; args: Map<string, GValue>; sel: GSel[] | null }
type GSel = { t: 'field'; f: GField } | { t: 'inline'; type: string | null; sel: GSel[] } | { t: 'spread'; name: string };
interface GOp { type: 'query' | 'mutation'; name: string | null; sel: GSel[] }

function gqlParse(doc: string): { ops: GOp[]; fragments: Map<string, { type: string | null; sel: GSel[] }> } {
  let i = 0;
  const n = doc.length;
  const skip = (): void => { while (i < n && (doc[i] === ' ' || doc[i] === '\n' || doc[i] === '\r' || doc[i] === '\t' || doc[i] === ',')) i++; if (doc[i] === '#') { while (i < n && doc[i] !== '\n') i++; skip(); } };
  const peek = (): string => { skip(); return doc[i] ?? ''; };
  const expect = (c: string): void => { skip(); if (doc[i] !== c) throw new Error(`expected ${c} at ${i}`); i++; };
  const readName = (): string => { skip(); const m = /^[_A-Za-z][_0-9A-Za-z]*/.exec(doc.slice(i)); if (!m) throw new Error(`expected name at ${i}`); i += m[0].length; return m[0]; };
  const readString = (): string => {
    if (doc.startsWith('"""', i)) { const end = doc.indexOf('"""', i + 3); const s = doc.slice(i + 3, end); i = end + 3; return s; }
    expect('"');
    let out = '';
    while (i < n && doc[i] !== '"') {
      if (doc[i] === '\\') { i++; const e = doc[i]; out += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e; i++; }
      else { out += doc[i]; i++; }
    }
    expect('"');
    return out;
  };
  const readValue = (): GValue => {
    skip();
    const c = doc[i];
    if (c === '$') { i++; return { k: 'var', v: readName() }; }
    if (c === '"') return { k: 'str', v: readString() };
    if (c === '[') { i++; const items: GValue[] = []; while (peek() !== ']') items.push(readValue()); expect(']'); return { k: 'list', v: items }; }
    if (c === '{') {
      i++; const obj = new Map<string, GValue>();
      while (peek() !== '}') { const key = readName(); expect(':'); obj.set(key, readValue()); }
      expect('}'); return { k: 'obj', v: obj };
    }
    if (c === '-' || (c >= '0' && c <= '9')) {
      const m = /^-?\d+(\.\d+)?([eE][+-]?\d+)?/.exec(doc.slice(i))!;
      i += m[0].length; return { k: 'num', v: Number(m[0]) };
    }
    const name = readName();
    if (name === 'true') return { k: 'bool', v: true };
    if (name === 'false') return { k: 'bool', v: false };
    if (name === 'null') return { k: 'null' };
    return { k: 'str', v: name }; // enum literal
  };
  const readArgs = (): Map<string, GValue> => {
    const args = new Map<string, GValue>();
    if (peek() !== '(') return args;
    expect('(');
    while (peek() !== ')') { const key = readName(); expect(':'); args.set(key, readValue()); }
    expect(')');
    return args;
  };
  const skipDirectives = (): void => { while (peek() === '@') { i++; readName(); readArgs(); } };
  const readSelection = (): GSel[] => {
    expect('{');
    const out: GSel[] = [];
    while (peek() !== '}') {
      skip();
      if (doc.startsWith('...', i)) {
        i += 3; skip();
        if (doc[i] === 'o' && doc[i + 1] === 'n' && !/[_0-9A-Za-z]/.test(doc[i + 2] ?? '')) {
          i += 2; const type = readName(); skipDirectives();
          out.push({ t: 'inline', type, sel: readSelection() });
        } else {
          const name = readName(); skipDirectives();
          out.push({ t: 'spread', name });
        }
        continue;
      }
      let name = readName();
      let alias: string | null = null;
      if (peek() === ':') { expect(':'); alias = name; name = readName(); }
      const args = readArgs();
      skipDirectives();
      let sel: GSel[] | null = null;
      if (peek() === '{') sel = readSelection();
      out.push({ t: 'field', f: { name, alias, args, sel } });
    }
    expect('}');
    return out;
  };
  const skipVarDefs = (): void => {
    if (peek() !== '(') return;
    let depth = 0;
    do { skip(); const c = doc[i]; if (c === '(') depth++; if (c === ')') depth--; if (c === '"') { readString(); continue; } i++; } while (depth > 0 && i < n);
  };
  const ops: GOp[] = [];
  const fragments = new Map<string, { type: string | null; sel: GSel[] }>();
  while (true) {
    skip();
    if (i >= n) break;
    if (doc[i] === '{') { ops.push({ type: 'query', name: null, sel: readSelection() }); continue; }
    const kw = readName();
    if (kw === 'query' || kw === 'mutation' || kw === 'subscription') {
      let name: string | null = null;
      skip();
      if (/[_A-Za-z]/.test(doc[i] ?? '')) name = readName();
      skipVarDefs(); skipDirectives();
      ops.push({ type: kw === 'mutation' ? 'mutation' : 'query', name, sel: readSelection() });
    } else if (kw === 'fragment') {
      const fname = readName();
      const onKw = readName();
      const type = onKw === 'on' ? readName() : null;
      skipDirectives();
      fragments.set(fname, { type, sel: readSelection() });
    } else throw new Error(`unexpected token ${kw}`);
  }
  return { ops, fragments };
}
function gval(v: GValue | undefined, vars: Record<string, unknown>): unknown {
  if (!v) return undefined;
  switch (v.k) {
    case 'var': return vars[v.v];
    case 'str': case 'num': case 'bool': return v.v;
    case 'null': return null;
    case 'list': return v.v.map((x) => gval(x, vars));
    case 'obj': { const o: Record<string, unknown> = {}; for (const [k, x] of v.v) o[k] = gval(x, vars); return o; }
  }
}

// type/field tables: validation + introspection
const GQL_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'search', '__type', '__schema', '__typename'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment', '__typename'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'description', 'isPrivate', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'createdAt', 'updatedAt', 'url', '__typename'],
  Issue: ['id', 'number', 'title', 'state', 'body', 'author', 'repository', 'labels', 'comments', 'createdAt', 'updatedAt', 'closedAt', 'url', '__typename'],
  PullRequest: ['id', 'number', 'title', 'state', 'body', 'author', 'repository', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'files', 'mergeCommit', 'mergedAt', 'createdAt', 'updatedAt', 'additions', 'deletions', 'changedFiles', '__typename'],
  User: ['id', 'login', 'name', 'email', 'url', '__typename'],
  Actor: ['login', 'url', '__typename'],
  Label: ['id', 'name', 'color', 'description', '__typename'],
  Comment: ['id', 'body', 'author', 'createdAt', 'updatedAt', '__typename'],
  IssueComment: ['id', 'body', 'author', 'createdAt', 'updatedAt', '__typename'],
  Ref: ['name', 'prefix', 'target', '__typename'],
  Commit: ['oid', 'id', 'message', 'messageHeadline', 'committedDate', '__typename'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor', '__typename'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', '__typename'],
  IssueEdge: ['node', 'cursor', '__typename'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', '__typename'],
  PullRequestEdge: ['node', 'cursor', '__typename'],
  LabelConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', '__typename'],
  LabelEdge: ['node', 'cursor', '__typename'],
  CommentConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', '__typename'],
  CommentEdge: ['node', 'cursor', '__typename'],
  PullRequestFile: ['path', 'additions', 'deletions', 'changeType', '__typename'],
  PullRequestFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', '__typename'],
  PullRequestFileEdge: ['node', 'cursor', '__typename'],
  CreateIssuePayload: ['issue', 'clientMutationId', '__typename'],
  CloseIssuePayload: ['issue', 'clientMutationId', '__typename'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId', '__typename'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId', '__typename'],
  AddCommentPayload: ['commentEdge', 'subject', 'clientMutationId', '__typename'],
  SearchResultItemConnection: ['nodes', 'edges', 'pageInfo', 'issueCount', 'codeCount', 'repositoryCount', '__typename'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', '__typename'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason', '__typename'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason', '__typename'],
  __InputValue: ['name', 'description', 'type', 'defaultValue', '__typename'],
  __Schema: ['types', 'queryType', 'mutationType', '__typename'],
};
const GQL_CHILD_TYPE: Record<string, Record<string, string>> = {
  Query: { viewer: 'User', repository: 'Repository', node: 'Node', search: 'SearchResultItemConnection', __type: '__Type', __schema: '__Schema' },
  Mutation: { createIssue: 'CreateIssuePayload', closeIssue: 'CloseIssuePayload', createPullRequest: 'CreatePullRequestPayload', mergePullRequest: 'MergePullRequestPayload', addComment: 'AddCommentPayload' },
  Repository: { owner: 'User', defaultBranchRef: 'Ref', issue: 'Issue', issues: 'IssueConnection', pullRequest: 'PullRequest', pullRequests: 'PullRequestConnection' },
  Issue: { author: 'User', repository: 'Repository', labels: 'LabelConnection', comments: 'CommentConnection' },
  PullRequest: { author: 'User', repository: 'Repository', files: 'PullRequestFileConnection', mergeCommit: 'Commit' },
  Ref: { target: 'Commit' },
  IssueConnection: { nodes: 'Issue', edges: 'IssueEdge', pageInfo: 'PageInfo' },
  IssueEdge: { node: 'Issue' },
  PullRequestConnection: { nodes: 'PullRequest', edges: 'PullRequestEdge', pageInfo: 'PageInfo' },
  PullRequestEdge: { node: 'PullRequest' },
  LabelConnection: { nodes: 'Label', edges: 'LabelEdge', pageInfo: 'PageInfo' },
  LabelEdge: { node: 'Label' },
  CommentConnection: { nodes: 'Comment', edges: 'CommentEdge', pageInfo: 'PageInfo' },
  CommentEdge: { node: 'Comment' },
  PullRequestFileConnection: { nodes: 'PullRequestFile', edges: 'PullRequestFileEdge', pageInfo: 'PageInfo' },
  PullRequestFileEdge: { node: 'PullRequestFile' },
  CreateIssuePayload: { issue: 'Issue' },
  CloseIssuePayload: { issue: 'Issue' },
  CreatePullRequestPayload: { pullRequest: 'PullRequest' },
  MergePullRequestPayload: { pullRequest: 'PullRequest' },
  AddCommentPayload: { commentEdge: 'CommentEdge', subject: 'Issue' },
  SearchResultItemConnection: { pageInfo: 'PageInfo' },
  __Type: { fields: '__Field', enumValues: '__EnumValue', possibleTypes: '__Type', inputFields: '__InputValue', ofType: '__Type' },
  __Field: { type: '__Type', args: '__InputValue' },
  __Schema: { types: '__Type', queryType: '__Type', mutationType: '__Type' },
};
const GQL_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  Permission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
};

type Src =
  | { t: 'root' } | { t: 'repo'; repo: Repo } | { t: 'issue'; repo: Repo; item: Issue }
  | { t: 'user'; login: string; id: number } | { t: 'label'; label: Label }
  | { t: 'comment'; repo: Repo; comment: Comment } | { t: 'ref'; repo: Repo; branch: string }
  | { t: 'commit'; oid: string } | { t: 'conn'; items: Src[]; cursors: string[]; total: number; hasNext: boolean; endCursor: string | null }
  | { t: 'edge'; node: Src; cursor: string } | { t: 'pageinfo'; hasNext: boolean; endCursor: string | null }
  | { t: 'file'; change: FileChange } | { t: 'payload'; fields: Record<string, Src | string | null> }
  | { t: 'gtype'; name: string } | { t: 'gfield'; name: string } | { t: 'genum'; name: string };

function cursorOf(n: number): string { return Buffer.from(`cursor:${n}`, 'utf8').toString('base64'); }
function connOf(items: Src[], keys: number[], args: Map<string, GValue>, vars: Record<string, unknown>): Src {
  let start = 0;
  const after = gval(args.get('after'), vars);
  if (typeof after === 'string') {
    const idx = keys.findIndex((k) => cursorOf(k) === after);
    if (idx >= 0) start = idx + 1;
    else {
      const m = /^cursor:(\d+)$/.exec(Buffer.from(after, 'base64').toString('utf8'));
      if (m) { const pos = keys.findIndex((k) => k === Number(m[1])); if (pos >= 0) start = pos + 1; }
    }
  }
  const firstRaw = gval(args.get('first'), vars);
  const first = typeof firstRaw === 'number' ? firstRaw : items.length;
  const pageItems = items.slice(start, start + first);
  const pageKeys = keys.slice(start, start + first);
  const hasNext = start + first < items.length;
  return {
    t: 'conn', items: pageItems, cursors: pageKeys.map(cursorOf), total: items.length,
    hasNext, endCursor: pageKeys.length ? cursorOf(pageKeys[pageKeys.length - 1]) : null,
  };
}
function sortIssues(list: Issue[], args: Map<string, GValue>, vars: Record<string, unknown>): Issue[] {
  const orderBy = gval(args.get('orderBy'), vars) as { field?: string; direction?: string } | undefined;
  const direction = orderBy?.direction === 'ASC' ? 'ASC' : 'DESC';
  const out = [...list];
  out.sort((a, b) => (direction === 'ASC' ? a.seq - b.seq : b.seq - a.seq));
  return out;
}

interface GqlCtx { errors: { message: string }[]; vars: Record<string, unknown>; fragments: Map<string, { type: string | null; sel: GSel[] }> }

function resolveField(src: Src, typeName: string, field: GField, ctx: GqlCtx): unknown {
  const arg = (k: string): unknown => gval(field.args.get(k), ctx.vars);
  if (field.name === '__typename') return typeName;
  switch (typeName) {
    case 'Query': {
      if (field.name === 'viewer') return { t: 'user', login: VIEWER.login, id: VIEWER.id } satisfies Src;
      if (field.name === 'repository') {
        const repo = findRepo(String(arg('owner') ?? ''), String(arg('name') ?? ''));
        return repo ? ({ t: 'repo', repo } satisfies Src) : null;
      }
      if (field.name === 'node') return nodeSrc(String(arg('id') ?? ''));
      if (field.name === 'search') return { t: 'conn', items: [], cursors: [], total: 0, hasNext: false, endCursor: null } satisfies Src;
      if (field.name === '__type') return { t: 'gtype', name: String(arg('name') ?? '') } satisfies Src;
      if (field.name === '__schema') return { t: 'payload', fields: {} } satisfies Src;
      break;
    }
    case 'Mutation': {
      if (field.name === 'createIssue') {
        const input = (arg('input') ?? {}) as Record<string, unknown>;
        const parts = parseGid(String(input.repositoryId ?? ''));
        const repo = parts && parts[0] === 'R' ? repoByDbId(Number(parts[1])) : undefined;
        if (!repo) { ctx.errors.push({ message: 'repository not found for createIssue' }); return null; }
        const issue: Issue = { kind: 'issue', id: nextIssueId++, number: repo.nextNumber++, title: String(input.title ?? ''), body: String(input.body ?? ''), state: 'open', labels: [], created: Date.now(), seq: seqCounter++ };
        repo.items.push(issue);
        return { t: 'payload', fields: { issue: { t: 'issue', repo, item: issue }, clientMutationId: (input.clientMutationId as string) ?? null } } satisfies Src;
      }
      if (field.name === 'closeIssue') {
        const input = (arg('input') ?? {}) as Record<string, unknown>;
        const found = issueFromGid(String(input.issueId ?? ''));
        if (!found) { ctx.errors.push({ message: 'issue not found for closeIssue' }); return null; }
        found.item.state = 'closed';
        return { t: 'payload', fields: { issue: { t: 'issue', repo: found.repo, item: found.item }, clientMutationId: (input.clientMutationId as string) ?? null } } satisfies Src;
      }
      if (field.name === 'createPullRequest') {
        const input = (arg('input') ?? {}) as Record<string, unknown>;
        const parts = parseGid(String(input.repositoryId ?? ''));
        const repo = parts && parts[0] === 'R' ? repoByDbId(Number(parts[1])) : undefined;
        if (!repo) { ctx.errors.push({ message: 'repository not found for createPullRequest' }); return null; }
        const strip = (r: string): string => r.replace(/^refs\/heads\//, '');
        const head = strip(String(input.headRefName ?? '')); const base = strip(String(input.baseRefName ?? ''));
        if (!branchTip(repo, head) || !branchTip(repo, base)) { ctx.errors.push({ message: 'head or base branch does not exist' }); return null; }
        const pull: Issue = { kind: 'pull', id: nextIssueId++, number: repo.nextNumber++, title: String(input.title ?? ''), body: String(input.body ?? ''), state: 'open', labels: [], created: Date.now(), seq: seqCounter++, headRef: head, baseRef: base, merged: false, mergedAt: null, mergeCommitSha: null };
        repo.items.push(pull);
        return { t: 'payload', fields: { pullRequest: { t: 'issue', repo, item: pull }, clientMutationId: (input.clientMutationId as string) ?? null } } satisfies Src;
      }
      if (field.name === 'mergePullRequest') {
        const input = (arg('input') ?? {}) as Record<string, unknown>;
        const found = issueFromGid(String(input.pullRequestId ?? ''));
        if (!found || found.item.kind !== 'pull') { ctx.errors.push({ message: 'pull request not found for mergePullRequest' }); return null; }
        const result = mergePull(found.repo, found.item);
        if (result === 'conflict' || result === 'gone') { ctx.errors.push({ message: 'Pull Request is not mergeable' }); return null; }
        return { t: 'payload', fields: { pullRequest: { t: 'issue', repo: found.repo, item: found.item }, clientMutationId: (input.clientMutationId as string) ?? null } } satisfies Src;
      }
      if (field.name === 'addComment') {
        const input = (arg('input') ?? {}) as Record<string, unknown>;
        const found = issueFromGid(String(input.subjectId ?? ''));
        if (!found) { ctx.errors.push({ message: 'subject not found for addComment' }); return null; }
        const comment: Comment = { id: nextCommentId++, body: String(input.body ?? ''), user: VIEWER.login, created: Date.now(), issueNumber: found.item.number };
        found.repo.comments.push(comment);
        const src: Src = { t: 'comment', repo: found.repo, comment };
        return { t: 'payload', fields: { commentEdge: { t: 'edge', node: src, cursor: cursorOf(comment.id) }, subject: { t: 'issue', repo: found.repo, item: found.item }, clientMutationId: (input.clientMutationId as string) ?? null } } satisfies Src;
      }
      break;
    }
    case 'Repository': {
      const repo = (src as { repo: Repo }).repo;
      switch (field.name) {
        case 'id': return gid('R', repo.id);
        case 'databaseId': return repo.id;
        case 'name': return repo.name;
        case 'nameWithOwner': return repoKey(repo.owner, repo.name);
        case 'owner': return { t: 'user', login: repo.owner, id: repo.owner === VIEWER.login ? VIEWER.id : 0 } satisfies Src;
        case 'description': return repo.description;
        case 'isPrivate': return repo.priv;
        case 'defaultBranchRef': return branchTip(repo, repo.defaultBranch) ? ({ t: 'ref', repo, branch: repo.defaultBranch } satisfies Src) : null;
        case 'viewerPermission': return repo.owner === VIEWER.login ? 'ADMIN' : 'READ';
        case 'hasIssuesEnabled': return true;
        case 'createdAt': case 'updatedAt': return new Date(repo.created).toISOString();
        case 'url': return `/${repo.owner}/${repo.name}`;
        case 'issue': {
          const item = repo.items.find((i) => i.kind === 'issue' && i.number === Number(arg('number')));
          return item ? ({ t: 'issue', repo, item } satisfies Src) : null;
        }
        case 'issues': {
          let list = repo.items.filter((i) => i.kind === 'issue');
          const states = gval(field.args.get('states'), ctx.vars) as string[] | undefined;
          if (Array.isArray(states)) list = list.filter((i) => states.includes(i.state.toUpperCase()));
          list = sortIssues(list, field.args, ctx.vars);
          return connOf(list.map((item) => ({ t: 'issue', repo, item } as Src)), list.map((i) => i.number), field.args, ctx.vars);
        }
        case 'pullRequest': {
          const item = repo.items.find((i) => i.kind === 'pull' && i.number === Number(arg('number')));
          return item ? ({ t: 'issue', repo, item } satisfies Src) : null;
        }
        case 'pullRequests': {
          let list = repo.items.filter((i) => i.kind === 'pull');
          const states = gval(field.args.get('states'), ctx.vars) as string[] | undefined;
          if (Array.isArray(states)) list = list.filter((i) => states.includes(i.merged ? 'MERGED' : i.state.toUpperCase()));
          list = sortIssues(list, field.args, ctx.vars);
          return connOf(list.map((item) => ({ t: 'issue', repo, item } as Src)), list.map((i) => i.number), field.args, ctx.vars);
        }
      }
      break;
    }
    case 'Issue': case 'PullRequest': {
      const { repo, item } = src as { repo: Repo; item: Issue };
      switch (field.name) {
        case 'id': return gid(item.kind === 'pull' ? 'P' : 'I', repo.id, item.number);
        case 'number': return item.number;
        case 'title': return item.title;
        case 'body': return item.body;
        case 'state': return item.kind === 'pull' && item.merged ? 'MERGED' : item.state.toUpperCase();
        case 'author': return { t: 'user', login: VIEWER.login, id: VIEWER.id } satisfies Src;
        case 'repository': return { t: 'repo', repo } satisfies Src;
        case 'createdAt': case 'updatedAt': return new Date(item.created).toISOString();
        case 'closedAt': return item.state === 'closed' ? new Date(item.created).toISOString() : null;
        case 'url': return `/${repo.owner}/${repo.name}/${item.kind === 'pull' ? 'pull' : 'issues'}/${item.number}`;
        case 'labels': {
          const labels = item.labels.map((n) => repo.labels.get(n)).filter((l): l is Label => Boolean(l));
          return connOf(labels.map((label) => ({ t: 'label', label } as Src)), labels.map((l) => l.id), field.args, ctx.vars);
        }
        case 'comments': {
          const list = repo.comments.filter((c) => c.issueNumber === item.number).sort((a, b) => a.id - b.id);
          return connOf(list.map((comment) => ({ t: 'comment', repo, comment } as Src)), list.map((c) => c.id), field.args, ctx.vars);
        }
        case 'merged': return item.merged === true;
        case 'mergedAt': return item.mergedAt ?? null;
        case 'mergeable': {
          if (item.merged) return 'MERGEABLE';
          return tryMerge(repo, item) ? 'MERGEABLE' : 'CONFLICTING';
        }
        case 'headRefName': return item.headRef ?? '';
        case 'baseRefName': return item.baseRef ?? '';
        case 'headRefOid': return item.headRef ? (branchTip(repo, item.headRef) ?? ZERO) : ZERO;
        case 'baseRefOid': return item.baseRef ? (branchTip(repo, item.baseRef) ?? ZERO) : ZERO;
        case 'files': {
          const files = pullFiles(repo, item);
          return connOf(files.map((change) => ({ t: 'file', change } as Src)), files.map((_, idx) => idx + 1), field.args, ctx.vars);
        }
        case 'mergeCommit': return item.mergeCommitSha ? ({ t: 'commit', oid: item.mergeCommitSha } satisfies Src) : null;
        case 'additions': return pullFiles(repo, item).reduce((s, f) => s + f.additions, 0);
        case 'deletions': return pullFiles(repo, item).reduce((s, f) => s + f.deletions, 0);
        case 'changedFiles': return pullFiles(repo, item).length;
      }
      break;
    }
    case 'User': case 'Actor': {
      const u = src as { login: string; id: number };
      if (field.name === 'id') return gid('U', u.id);
      if (field.name === 'login') return u.login;
      if (field.name === 'name') return u.login === VIEWER.login ? VIEWER.name : u.login;
      if (field.name === 'email') return u.login === VIEWER.login ? VIEWER.email : '';
      if (field.name === 'url') return `/${u.login}`;
      break;
    }
    case 'Label': {
      const l = (src as { label: Label }).label;
      if (field.name === 'id') return gid('L', l.id);
      if (field.name === 'name') return l.name;
      if (field.name === 'color') return l.color;
      if (field.name === 'description') return l.description;
      break;
    }
    case 'Comment': case 'IssueComment': {
      const c = (src as { comment: Comment }).comment;
      if (field.name === 'id') return gid('C', c.id);
      if (field.name === 'body') return c.body;
      if (field.name === 'author') return { t: 'user', login: c.user, id: VIEWER.id } satisfies Src;
      if (field.name === 'createdAt' || field.name === 'updatedAt') return new Date(c.created).toISOString();
      break;
    }
    case 'Ref': {
      const r = src as { repo: Repo; branch: string };
      if (field.name === 'name') return r.branch;
      if (field.name === 'prefix') return 'refs/heads/';
      if (field.name === 'target') { const tip = branchTip(r.repo, r.branch); return tip ? ({ t: 'commit', oid: tip } satisfies Src) : null; }
      break;
    }
    case 'Commit': {
      const oid = (src as { oid: string }).oid;
      const c = commitOf(oid);
      if (field.name === 'oid' || field.name === 'id') return oid;
      if (field.name === 'message' || field.name === 'messageHeadline') return c ? c.message.split('\n')[0] : '';
      if (field.name === 'committedDate') return c ? new Date(c.ts * 1000).toISOString() : null;
      break;
    }
    case 'PageInfo': {
      const p = src as { hasNext: boolean; endCursor: string | null };
      if (field.name === 'hasNextPage') return p.hasNext;
      if (field.name === 'hasPreviousPage') return false;
      if (field.name === 'endCursor') return p.endCursor;
      if (field.name === 'startCursor') return p.endCursor;
      break;
    }
    case 'PullRequestFile': {
      const f = (src as { change: FileChange }).change;
      if (field.name === 'path') return f.filename;
      if (field.name === 'additions') return f.additions;
      if (field.name === 'deletions') return f.deletions;
      if (field.name === 'changeType') return f.status.toUpperCase();
      break;
    }
    case '__Type': {
      const name = (src as { name: string }).name;
      if (field.name === 'name') return name;
      if (field.name === 'kind') return GQL_ENUMS[name] ? 'ENUM' : 'OBJECT';
      if (field.name === 'description') return null;
      if (field.name === 'fields') {
        const includeDeprecated = gval(field.args.get('includeDeprecated'), ctx.vars);
        void includeDeprecated;
        const list = GQL_FIELDS[name];
        return list ? list.filter((f) => f !== '__typename').map((fname) => ({ t: 'gfield', name: fname } as Src)) : null;
      }
      if (field.name === 'enumValues') {
        const vals = GQL_ENUMS[name];
        return vals ? vals.map((v) => ({ t: 'genum', name: v } as Src)) : null;
      }
      if (field.name === 'possibleTypes' || field.name === 'inputFields') return [];
      if (field.name === 'ofType') return null;
      break;
    }
    case '__Field': {
      const f = src as { name: string };
      if (field.name === 'name') return f.name;
      if (field.name === 'description') return null;
      if (field.name === 'args') return [];
      if (field.name === 'type') return { t: 'gtype', name: 'String' } satisfies Src;
      if (field.name === 'isDeprecated') return false;
      if (field.name === 'deprecationReason') return null;
      break;
    }
    case '__EnumValue': {
      const e = src as { name: string };
      if (field.name === 'name') return e.name;
      if (field.name === 'description') return null;
      if (field.name === 'isDeprecated') return false;
      if (field.name === 'deprecationReason') return null;
      break;
    }
    case '__Schema': {
      if (field.name === 'types') return Object.keys(GQL_FIELDS).map((name) => ({ t: 'gtype', name } as Src));
      if (field.name === 'queryType') return { t: 'gtype', name: 'Query' } satisfies Src;
      if (field.name === 'mutationType') return { t: 'gtype', name: 'Mutation' } satisfies Src;
      break;
    }
  }
  if (src.t === 'payload') {
    const v = (src as { fields: Record<string, Src | string | null> }).fields[field.name];
    return v === undefined ? null : v;
  }
  if (src.t === 'conn') {
    const c = src as Extract<Src, { t: 'conn' }>;
    if (field.name === 'nodes') return c.items;
    if (field.name === 'edges') return c.items.map((node, idx) => ({ t: 'edge', node, cursor: c.cursors[idx] } as Src));
    if (field.name === 'pageInfo') return { t: 'pageinfo', hasNext: c.hasNext, endCursor: c.endCursor } satisfies Src;
    if (field.name === 'totalCount' || field.name === 'issueCount' || field.name === 'codeCount' || field.name === 'repositoryCount') return c.total;
  }
  if (src.t === 'edge') {
    const e = src as Extract<Src, { t: 'edge' }>;
    if (field.name === 'node') return e.node;
    if (field.name === 'cursor') return e.cursor;
  }
  return null;
}
function issueFromGid(id: string): { repo: Repo; item: Issue } | null {
  const parts = parseGid(id);
  if (!parts || (parts[0] !== 'I' && parts[0] !== 'P')) return null;
  const repo = repoByDbId(Number(parts[1]));
  if (!repo) return null;
  const item = repo.items.find((i) => i.number === Number(parts[2]));
  return item ? { repo, item } : null;
}
function nodeSrc(id: string): Src | null {
  const parts = parseGid(id);
  if (!parts) return null;
  if (parts[0] === 'R') { const repo = repoByDbId(Number(parts[1])); return repo ? { t: 'repo', repo } : null; }
  if (parts[0] === 'I' || parts[0] === 'P') { const f = issueFromGid(id); return f ? { t: 'issue', repo: f.repo, item: f.item } : null; }
  if (parts[0] === 'U') return { t: 'user', login: VIEWER.login, id: VIEWER.id };
  if (parts[0] === 'C') {
    for (const repo of repos.values()) {
      const comment = repo.comments.find((c) => c.id === Number(parts[1]));
      if (comment) return { t: 'comment', repo, comment };
    }
  }
  return null;
}
function srcTypeName(src: Src): string {
  switch (src.t) {
    case 'repo': return 'Repository';
    case 'issue': return src.item.kind === 'pull' ? 'PullRequest' : 'Issue';
    case 'user': return 'User';
    case 'label': return 'Label';
    case 'comment': return 'IssueComment';
    case 'ref': return 'Ref';
    case 'commit': return 'Commit';
    case 'file': return 'PullRequestFile';
    case 'gtype': return '__Type';
    case 'gfield': return '__Field';
    case 'genum': return '__EnumValue';
    case 'pageinfo': return 'PageInfo';
    case 'edge': return 'Edge';
    case 'conn': return 'Connection';
    default: return 'Query';
  }
}
function execSelection(src: Src | null, typeName: string, sel: GSel[], ctx: GqlCtx): Record<string, unknown> | null {
  if (src === null) return null;
  const out: Record<string, unknown> = {};
  const walk = (sels: GSel[], curType: string, cur: Src): void => {
    for (const s of sels) {
      if (s.t === 'inline') {
        if (!s.type || s.type === curType || s.type === 'Node' || s.type === 'Actor') walk(s.sel, s.type ?? curType, cur);
        continue;
      }
      if (s.t === 'spread') {
        const frag = ctx.fragments.get(s.name);
        if (frag) walk(frag.sel, frag.type ?? curType, cur);
        continue;
      }
      const f = s.f;
      const key = f.alias ?? f.name;
      const known = (GQL_FIELDS[curType] ?? []).includes(f.name);
      if (!known) {
        ctx.errors.push({ message: `Field '${f.name}' doesn't exist on type '${curType}'` });
        out[key] = null;
        continue;
      }
      const value = resolveField(cur, curType, f, ctx);
      const childType = GQL_CHILD_TYPE[curType]?.[f.name] ?? curType;
      if (f.sel && value !== null && value !== undefined) {
        if (Array.isArray(value)) {
          out[key] = value.map((v) => (typeof v === 'object' && v !== null && 't' in v ? execSelection(v as Src, childType === 'Node' ? srcTypeName(v as Src) : childType, f.sel!, ctx) : v));
        } else if (typeof value === 'object' && 't' in (value as Src)) {
          const vs = value as Src;
          out[key] = execSelection(vs, childType === 'Node' ? srcTypeName(vs) : childType, f.sel, ctx);
        } else out[key] = value;
      } else {
        out[key] = value ?? null;
      }
    }
  };
  walk(sel, typeName, src);
  return out;
}

async function handleGraphql(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const raw = await readBody(req);
  if (!authed(req)) { sendJson(res, 401, { message: 'Bad credentials' }); return; }
  let parsed: unknown;
  try { parsed = JSON.parse(raw.toString('utf8')); }
  catch { sendJson(res, 400, { message: 'Problems parsing JSON' }); return; }
  const runOne = (op: Record<string, unknown>): Record<string, unknown> => {
    const query = String(op.query ?? '');
    const vars = (op.variables ?? {}) as Record<string, unknown>;
    const opName = typeof op.operationName === 'string' ? op.operationName : null;
    let doc: { ops: GOp[]; fragments: Map<string, { type: string | null; sel: GSel[] }> };
    try { doc = gqlParse(query); }
    catch (e) { return { data: null, errors: [{ message: `Parse error: ${(e as Error).message}` }] }; }
    const operation = doc.ops.find((o) => (opName ? o.name === opName : true)) ?? doc.ops[0];
    if (!operation) return { data: null, errors: [{ message: 'no operation found' }] };
    const ctx: GqlCtx = { errors: [], vars, fragments: doc.fragments };
    const rootType = operation.type === 'mutation' ? 'Mutation' : 'Query';
    const data = execSelection({ t: 'root' }, rootType, operation.sel, ctx);
    const out: Record<string, unknown> = { data };
    if (ctx.errors.length) out.errors = ctx.errors;
    return out;
  };
  if (Array.isArray(parsed)) { sendJson(res, 200, parsed.map((op) => runOne(op as Record<string, unknown>))); return; }
  sendJson(res, 200, runOne(parsed as Record<string, unknown>));
}

// --------------------------------------------------------------------------- git smart-HTTP

type PktToken = { t: 'data'; payload: Buffer } | { t: 'flush' } | { t: 'delim' } | { t: 'end' };
function parsePktStream(buf: Buffer, start = 0): { tokens: PktToken[]; rest: number } {
  const tokens: PktToken[] = [];
  let off = start;
  while (off + 4 <= buf.length) {
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error('bad pkt-line');
    const len = parseInt(hex, 16);
    if (len === 0) { tokens.push({ t: 'flush' }); off += 4; continue; }
    if (len === 1) { tokens.push({ t: 'delim' }); off += 4; continue; }
    if (len === 2) { tokens.push({ t: 'end' }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) throw new Error('pkt-line overrun');
    tokens.push({ t: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { tokens, rest: off };
}
function derefTag(oid: string): string {
  let cur = oid;
  for (let i = 0; i < 10; i++) {
    const o = getObject(cur);
    if (!o || o.type !== 'tag') break;
    const m = /^object ([0-9a-f]{40})/m.exec(o.data.toString('utf8'));
    if (!m) break;
    cur = m[1];
  }
  return cur;
}
function sortedRefs(repo: Repo): [string, string][] {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
}
function v0Advertisement(repo: Repo, service: string): Buffer {
  const caps = service === 'git-upload-pack'
    ? 'multi_ack_detailed side-band-64k thin-pack ofs-delta shallow agent=forge/1.0 symref=HEAD:refs/heads/main'
    : 'report-status delete-refs side-band-64k ofs-delta agent=forge/1.0 symref=HEAD:refs/heads/main';
  const parts: Buffer[] = [pkt(`# service=${service}\n`), PKT_FLUSH];
  const lines: string[] = [];
  const headTip = branchTip(repo, repo.defaultBranch);
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    lines.push(`${ZERO} capabilities^{}`);
  } else {
    lines.push(`${headTip ?? ZERO} HEAD`);
    for (const [ref, oid] of refs) {
      lines.push(`${oid} ${ref}`);
      const peeled = derefTag(oid);
      if (peeled !== oid) lines.push(`${peeled} ${ref}^{}`);
    }
  }
  lines.forEach((line, idx) => {
    parts.push(pkt(idx === 0 ? `${line}\0${caps}\n` : `${line}\n`));
  });
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}
function treeClosure(rootTree: string | null, into: Set<string>): void {
  if (!rootTree || into.has(rootTree)) return;
  const o = getObject(rootTree);
  if (!o || o.type !== 'tree') return;
  into.add(rootTree);
  for (const e of treeEntries(rootTree, o.data)) {
    if (e.mode === '40000') treeClosure(e.oid, into);
    else into.add(e.oid);
  }
}
function objectsForCommits(commits: string[], exclude: Set<string>): { oid: string; obj: Obj }[] {
  const picked = new Map<string, Obj>();
  const add = (oid: string): void => {
    if (exclude.has(oid) || picked.has(oid)) return;
    const o = getObject(oid);
    if (o) picked.set(oid, o);
  };
  for (const c of commits) {
    add(c);
    const info = commitOf(c);
    if (info) {
      const closure = new Set<string>();
      treeClosure(info.tree, closure);
      for (const oid of closure) add(oid);
    }
  }
  return [...picked.entries()].map(([oid, obj]) => ({ oid, obj }));
}
/**
 * A pack is a pure function of its ordered object list (writePack is deterministic and the
 * objects are immutable), so identical fetches — e.g. a burst of clones of one tip — reuse
 * the bytes instead of re-deflating every object. The cache is small and simply cleared
 * when full; correctness never depends on it.
 */
const packCache = new Map<string, Buffer>();
function packForList(list: { oid: string; obj: Obj }[]): Buffer {
  const key = list.map((p) => p.oid).join(' ');
  const hit = packCache.get(key);
  if (hit) return hit;
  const pack = writePack(list.map((p) => p.obj));
  if (packCache.size >= 64) packCache.clear();
  packCache.set(key, pack);
  return pack;
}
function closureOfCommits(commits: string[]): Set<string> {
  const out = new Set<string>();
  for (const c of commits) {
    out.add(c);
    const info = commitOf(c);
    if (info) treeClosure(info.tree, out);
  }
  return out;
}
/** BFS layers from tips: returns commits grouped by depth (1-based); maxDepth stops the walk early. */
function commitLayers(tips: string[], boundary: Set<string>, maxDepth = Infinity): Map<string, number> {
  const depth = new Map<string, number>();
  let frontier = tips.filter((t) => getObject(t)?.type === 'commit');
  let d = 1;
  while (frontier.length) {
    const next: string[] = [];
    for (const oid of frontier) {
      if (depth.has(oid)) continue;
      depth.set(oid, d);
      if (!boundary.has(oid) && d < maxDepth) {
        const c = commitOf(oid);
        if (c) next.push(...c.parents);
      }
    }
    frontier = next; d++;
  }
  return depth;
}

interface FetchPlan { pack: Buffer; shallow: string[]; unshallow: string[] }
function planFetch(repo: Repo, wants: string[], haves: string[], clientShallow: string[], depth?: number, deepenSince?: number, deepenNot?: string[]): FetchPlan {
  const haveCommits = new Set(reachableCommits(haves));
  const exclude = closureOfCommits([...haves]);
  for (const s of clientShallow) for (const oid of closureOfCommits([s])) exclude.add(oid);
  const boundary = new Set(clientShallow);
  let commits: string[] = [];
  let shallow: string[] = [];
  let unshallow: string[] = [];
  if (depth !== undefined) {
    const layers = commitLayers(wants, new Set(), depth);
    commits = [...layers.entries()].filter(([, d]) => d <= depth).map(([oid]) => oid);
    const boundarySet = new Set(commits.filter((oid) => layers.get(oid) === depth && (commitOf(oid)?.parents.length ?? 0) > 0));
    shallow = [...boundarySet];
    unshallow = clientShallow.filter((s) => commits.includes(s) && !boundarySet.has(s));
  } else if (deepenSince !== undefined) {
    const all = commitLayers(wants, boundary);
    commits = [...all.keys()].filter((oid) => (commitOf(oid)?.ts ?? 0) > deepenSince && !haveCommits.has(oid));
    shallow = commits.filter((oid) => (commitOf(oid)?.parents ?? []).some((p) => !commits.includes(p)));
  } else {
    const notSet = new Set<string>();
    for (const nd of deepenNot ?? []) {
      const tip = refTip(repo, nd) ?? nd;
      for (const oid of reachableCommits([tip])) notSet.add(oid);
    }
    const layers = commitLayers(wants, boundary);
    commits = [...layers.keys()].filter((oid) => !haveCommits.has(oid) && !notSet.has(oid));
  }
  const packObjs = objectsForCommits(commits, exclude);
  const inPack = new Set(packObjs.map((p) => p.oid));
  for (const w of wants) {
    let cur = w;
    for (let i = 0; i < 10; i++) {
      const o = getObject(cur);
      if (!o || o.type !== 'tag' || exclude.has(cur) || inPack.has(cur)) break;
      packObjs.push({ oid: cur, obj: o }); inPack.add(cur);
      cur = derefTag(cur);
      if (cur === w) break;
    }
  }
  const pack = packForList(packObjs);
  return { pack, shallow, unshallow };
}
function sidebandPackets(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 60000;
  for (let i = 0; i < pack.length; i += CHUNK) {
    out.push(pkt(Buffer.concat([Buffer.from([1]), pack.subarray(i, i + CHUNK)])));
  }
  if (pack.length === 0) out.push(pkt(Buffer.from([1])));
  return out;
}

async function handleGit(req: IncomingMessage, res: ServerResponse, url: URL, owner: string, name: string, kind: string): Promise<void> {
  const repo = findRepo(owner, name);
  if (kind === 'info/refs') {
    if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return; }
    const service = url.searchParams.get('service') ?? '';
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { sendJson(res, 400, { message: 'bad service' }); return; }
    if (service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '').includes('version=2')) {
      const body = Buffer.concat([
        pkt('# service=git-upload-pack\n'), PKT_FLUSH,
        pkt('version 2\n'), pkt('agent=forge/1.0\n'), pkt('ls-refs=unborn\n'),
        pkt('fetch=shallow wait-for-done\n'), pkt('object-format=sha1\n'), PKT_FLUSH,
      ]);
      sendRaw(res, 200, body, 'application/x-git-upload-pack-advertisement');
      return;
    }
    sendRaw(res, 200, v0Advertisement(repo, service), `application/x-${service}-advertisement`);
    return;
  }
  const raw = await readBody(req);
  if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return; }

  if (kind === 'git-upload-pack') {
    try {
      const { tokens, rest } = parsePktStream(raw);
      void rest;
      const lines: string[] = [];
      for (const t of tokens) if (t.t === 'data') lines.push(t.payload.toString('utf8').replace(/\n$/, ''));
      const firstData = lines[0] ?? '';
      if (firstData === 'command=ls-refs') {
        const args = lines.slice(1);
        const prefixes = args.filter((a) => a.startsWith('ref-prefix ')).map((a) => a.slice('ref-prefix '.length));
        const wantPeel = args.includes('peel');
        const wantSymrefs = args.includes('symrefs');
        const wantUnborn = args.includes('unborn');
        const match = (ref: string): boolean => prefixes.length === 0 || prefixes.some((p) => ref.startsWith(p));
        const out: Buffer[] = [];
        const headTip = branchTip(repo, repo.defaultBranch);
        if (match('HEAD')) {
          if (headTip) out.push(pkt(`${headTip} HEAD${wantSymrefs ? ` symref-target:refs/heads/${repo.defaultBranch}` : ''}\n`));
          else if (wantUnborn) out.push(pkt(`unborn HEAD${wantSymrefs ? ` symref-target:refs/heads/${repo.defaultBranch}` : ''}\n`));
        }
        for (const [ref, oid] of sortedRefs(repo)) {
          if (!match(ref)) continue;
          let line = `${oid} ${ref}`;
          if (wantPeel) { const peeled = derefTag(oid); if (peeled !== oid) line += ` peeled:${peeled}`; }
          out.push(pkt(`${line}\n`));
        }
        out.push(PKT_FLUSH);
        sendRaw(res, 200, Buffer.concat(out), 'application/x-git-upload-pack-result');
        return;
      }
      if (firstData === 'command=fetch') {
        const args = lines.slice(1);
        const wants: string[] = []; const haves: string[] = []; const shallow: string[] = []; const deepenNot: string[] = [];
        let depth: number | undefined; let deepenSince: number | undefined;
        for (const a of args) {
          if (a.startsWith('want ')) wants.push(a.slice(5).trim());
          else if (a.startsWith('have ')) haves.push(a.slice(5).trim());
          else if (a.startsWith('shallow ')) shallow.push(a.slice(8).trim());
          else if (a.startsWith('deepen ')) depth = Number(a.slice(7));
          else if (a.startsWith('deepen-since ')) deepenSince = Number(a.slice(13));
          else if (a.startsWith('deepen-not ')) deepenNot.push(a.slice(11).trim());
        }
        const plan = planFetch(repo, wants, haves, shallow, depth, deepenSince, deepenNot);
        const parts: Buffer[] = [];
        const common = haves.filter((h) => getObject(h)?.type === 'commit');
        parts.push(pkt('acknowledgments\n'));
        if (common.length) parts.push(pkt(`ACK ${common[0]}\n`));
        else parts.push(pkt('NAK\n'));
        parts.push(PKT_FLUSH);
        if (plan.shallow.length || plan.unshallow.length) {
          parts.push(pkt('shallow-info\n'));
          for (const s of plan.shallow) parts.push(pkt(`shallow ${s}\n`));
          for (const s of plan.unshallow) parts.push(pkt(`unshallow ${s}\n`));
          parts.push(PKT_FLUSH);
        }
        parts.push(pkt('packfile\n'));
        parts.push(...sidebandPackets(plan.pack));
        parts.push(PKT_FLUSH);
        sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
        return;
      }
      if (lines.some((l) => l.startsWith('want '))) {
        // v0 fetch: wants section, then negotiation section
        const wants: string[] = []; const haves: string[] = []; const shallow: string[] = []; const deepenNot: string[] = [];
        let depth: number | undefined; let deepenSince: number | undefined;
        for (const l of lines) {
          const clean = l.split(' ')[0] === 'want' ? l : l;
          if (clean.startsWith('want ')) wants.push(clean.split(' ')[1]);
          else if (clean.startsWith('have ')) haves.push(clean.slice(5).trim());
          else if (clean.startsWith('shallow ')) shallow.push(clean.slice(8).trim());
          else if (clean.startsWith('deepen ')) depth = Number(clean.slice(7));
          else if (clean.startsWith('deepen-since ')) deepenSince = Number(clean.slice(13));
          else if (clean.startsWith('deepen-not ')) deepenNot.push(clean.slice(11).trim());
        }
        const plan = planFetch(repo, wants, haves, shallow, depth, deepenSince, deepenNot);
        const parts: Buffer[] = [];
        for (const s of plan.shallow) parts.push(pkt(`shallow ${s}\n`));
        for (const s of plan.unshallow) parts.push(pkt(`unshallow ${s}\n`));
        const common = haves.filter((h) => getObject(h)?.type === 'commit');
        parts.push(pkt(common.length ? `ACK ${common[0]}\n` : 'NAK\n'));
        parts.push(...sidebandPackets(plan.pack));
        parts.push(PKT_FLUSH);
        sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
        return;
      }
      sendRaw(res, 400, Buffer.from('error: unsupported upload-pack request\n'), 'application/x-git-upload-pack-result');
      return;
    } catch {
      sendRaw(res, 400, Buffer.from('error: malformed upload-pack request\n'), 'application/x-git-upload-pack-result');
      return;
    }
  }

  if (kind === 'git-receive-pack') {
    try {
      const commands: { oldOid: string; newOid: string; ref: string }[] = [];
      let caps = '';
      let off = 0;
      while (off + 4 <= raw.length) {
        const hex = raw.subarray(off, off + 4).toString('ascii');
        if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
        const len = parseInt(hex, 16);
        if (len === 0) { off += 4; break; }
        if (len < 4) { off += 4; continue; }
        let line = raw.subarray(off + 4, off + len).toString('utf8').replace(/\n$/, '');
        off += len;
        const nul = line.indexOf('\0');
        if (nul >= 0) { caps = line.slice(nul + 1); line = line.slice(0, nul); }
        const [oldOid, newOid, ref] = line.split(' ');
        if (oldOid && newOid && ref) commands.push({ oldOid, newOid, ref });
      }
      const rest = off;
      const packBytes = raw.subarray(rest);
      let unpackOk = true;
      if (packBytes.length > 0) {
        try { readPackIntoStore(packBytes); } catch { unpackOk = false; }
      }
      const reports: string[] = [];
      for (const cmd of commands) {
        const current = repo.refs.get(cmd.ref) ?? ZERO;
        let ok = false; let reason = '';
        if (!unpackOk) { reason = 'unpack failed'; }
        else if (cmd.newOid === ZERO) {
          if (current !== ZERO && cmd.oldOid === current) ok = true;
          else if (current === ZERO) { ok = false; reason = 'reference does not exist'; }
          else { reason = 'stale info'; }
        } else if (!getObject(cmd.newOid)) { reason = 'missing object'; }
        else if (current !== ZERO && !isAncestor(current, cmd.newOid) && current !== cmd.newOid) { reason = 'non-fast-forward'; }
        else if (cmd.oldOid !== ZERO && cmd.oldOid !== current && current !== ZERO) { reason = 'stale info'; }
        else ok = true;
        if (ok) {
          if (cmd.newOid === ZERO) repo.refs.delete(cmd.ref);
          else repo.refs.set(cmd.ref, cmd.newOid);
        }
        reports.push(ok ? `ok ${cmd.ref}` : `ng ${cmd.ref} ${reason}`);
      }
      const reportParts: Buffer[] = [pkt(unpackOk ? 'unpack ok\n' : 'unpack error\n'), ...reports.map((r) => pkt(`${r}\n`)), PKT_FLUSH];
      const report = Buffer.concat(reportParts);
      if (caps.includes('side-band-64k')) {
        const wrapped: Buffer[] = [];
        const CHUNK = 60000;
        for (let i = 0; i < report.length; i += CHUNK) wrapped.push(pkt(Buffer.concat([Buffer.from([1]), report.subarray(i, i + CHUNK)])));
        wrapped.push(PKT_FLUSH);
        sendRaw(res, 200, Buffer.concat(wrapped), 'application/x-git-receive-pack-result');
      } else {
        sendRaw(res, 200, report, 'application/x-git-receive-pack-result');
      }
      return;
    } catch {
      sendRaw(res, 400, Buffer.from('error: malformed receive-pack request\n'), 'application/x-git-receive-pack-result');
      return;
    }
  }
  sendJson(res, 404, { message: 'Not Found' });
}

// --------------------------------------------------------------------------- router

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    (async (): Promise<void> => {
      const url = new URL(req.url ?? '/', 'http://entry');
      const path = url.pathname;
      const method = req.method ?? 'GET';
      if (method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
      if (path === '/api/v3' || path.startsWith('/api/v3/')) {
        const seg = path.replace(/^\/api\/v3\/?/, '').split('/').filter((s) => s !== '');
        await handleRest(req, res, url, seg.map((s) => { try { return decodeURIComponent(s); } catch { return s; } }));
        return;
      }
      if (path === '/api/graphql' && method === 'POST') { await handleGraphql(req, res); return; }
      if (path === '/mcp' && method === 'POST') { await handleMcp(req, res); return; }
      const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(path);
      if (gitMatch) {
        if (!authed(req)) { sendJson(res, 401, { message: 'Bad credentials' }); return; }
        await handleGit(req, res, url, decodeURIComponent(gitMatch[1]), decodeURIComponent(gitMatch[2]), gitMatch[3]);
        return;
      }
      sendJson(res, 404, { message: 'Not Found' });
    })().catch(() => {
      if (!res.headersSent) sendJson(res, 500, { message: 'Internal Server Error' });
      else res.end();
    });
  });
}
