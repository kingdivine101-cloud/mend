// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file's lines under section 3: its line break, its lines, whether it ends with a break. */
interface FileLines {
  br: string;
  lines: string[];
  finalBreak: boolean;
}
function fileLines(text: string): FileLines {
  if (text === '') return { br: '\n', lines: [], finalBreak: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { br, lines: parts, finalBreak };
}
function writeLines(f: FileLines): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.finalBreak ? f.br : '');
}

const trailWs = (s: string): string => s.replace(/[ \t]+$/, '');
const bothWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => /^[ \t]*/.exec(s)![0];
function tierEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trailWs(a) === trailWs(b);
  return bothWs(a) === bothWs(b);
}
/** All 0-based positions where O occurs in lines at tier. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!tierEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}
/** The first tier (0, 1, 2; strict: only 0) at which O occurs, with its positions; null when none. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; positions: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const p = occurrences(lines, o, t);
    if (p.length > 0) return { tier: t, positions: p };
  }
  return null;
}
/** Section 5, tier 2: re-indent one new line from O's frame (P) to the file's frame (F). */
function reindentOne(line: string, oFirst: string, fFirst: string, tier: number): string {
  if (tier !== 2) return line;
  if (line === '' || line.trim() === '') return line;
  const p = leadWs(oFirst);
  const f = leadWs(fFirst);
  return line.startsWith(p) ? f + line.slice(p.length) : line;
}

/** One body line of a unified hunk or a V4A chunk: context, old, new, or a `\` line. */
interface BodyItem {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
  /** True when the patch line was empty (a context line with empty text written bare). */
  bare?: boolean;
}
/** Apply a hunk/chunk body at position pos (O's occurrence), writing context lines as the file's own. */
function applyBody(lines: string[], items: BodyItem[], pos: number, tier: number): string[] {
  const first = items.find((i) => i.kind === 'ctx' || i.kind === 'old');
  const out: string[] = [];
  let k = pos;
  for (const it of items) {
    if (it.kind === 'bs') continue;
    if (it.kind === 'ctx') {
      out.push(lines[k]!);
      k++;
    } else if (it.kind === 'old') {
      k++;
    } else if (first === undefined) {
      out.push(it.text);
    } else {
      out.push(reindentOne(it.text, first.text, lines[pos]!, tier));
    }
  }
  return out;
}
/** Whether a `\` line follows the hunk's last context or `+` line. */
function backslashAfterLast(lines: BodyItem[]): boolean {
  for (let i = lines.length - 1; i >= 0; i--) {
    const it = lines[i]!;
    if (it.kind === 'ctx' || it.kind === 'new') return lines[i + 1]?.kind === 'bs';
  }
  return false;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful move edits, as [old, new] pairs, for the R lines of section 2. */
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** Section 6: a unified diff section and its hunks. Paths are strings, or null for /dev/null, or undefined when unnamed. */
interface Hunk {
  a: number;
  items: BodyItem[];
}
interface UniSection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  gitOld: string | null | undefined;
  gitNew: string | null | undefined;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

/** The path after `--- ` or `+++ `: text after the four characters, up to the first tab, spaces removed, a/ or b/ stripped. */
function uniPath(line: string): string | null {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p === '/dev/null' ? null : p;
}
function isDiffGit(line: string): boolean {
  return line.startsWith('diff --git ');
}
function diffGitPaths(line: string): [string, string] | null {
  const rest = line.slice('diff --git '.length);
  if (!rest.startsWith('a/')) return null;
  const at = rest.indexOf(' b/');
  if (at < 0) return null;
  const x = rest.slice(2, at);
  const y = rest.slice(at + 3).trim();
  if (x === '' || y === '') return null;
  return [x, y];
}
function hunkHead(line: string): number | null {
  const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
  return m === null ? null : parseInt(m[1]!, 10);
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let curHunk: Hunk | null = null;
  const flushBody = (): void => {
    if (curHunk !== null && cur !== null) {
      while (curHunk.items.length > 0) {
        const last = curHunk.items[curHunk.items.length - 1]!;
        if (last.kind === 'ctx' && last.bare === true) curHunk.items.pop();
        else break;
      }
      cur.hunks.push(curHunk);
      curHunk = null;
    }
  };
  const bodyItem = (line: string): BodyItem | null => {
    if (line === '') return { kind: 'ctx', text: '', bare: true };
    const c = line[0]!;
    if (c === ' ') return { kind: 'ctx', text: line.slice(1) };
    if (c === '-') return { kind: 'old', text: line.slice(1) };
    if (c === '+') return { kind: 'new', text: line.slice(1) };
    if (c === '\\') return { kind: 'bs', text: line.slice(1) };
    return null;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (curHunk !== null) {
      if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        flushBody();
      } else {
        const it = bodyItem(line);
        if (it !== null) {
          curHunk.items.push(it);
          i++;
          continue;
        }
        flushBody();
      }
    }
    if (isDiffGit(line)) {
      const paths = diffGitPaths(line);
      if (paths === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { pairOld: undefined, pairNew: undefined, renameFrom: undefined, renameTo: undefined, gitOld: paths[0], gitNew: paths[1], isCreate: false, isDelete: false, hunks: [] };
      sections.push(cur);
      i++;
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && cur.pairOld === undefined && cur.hunks.length === 0) {
        cur.pairOld = uniPath(line);
        cur.pairNew = uniPath(lines[i + 1]!);
        i += 2;
      } else {
        cur = { pairOld: uniPath(line), pairNew: uniPath(lines[i + 1]!), renameFrom: undefined, renameTo: undefined, gitOld: undefined, gitNew: undefined, isCreate: false, isDelete: false, hunks: [] };
        sections.push(cur);
        i += 2;
      }
    } else if (line.startsWith('--- ') && cur !== null && cur.hunks.length === 0) {
      throw new Exit2(`error: parse ${i + 2}`);
    } else if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = hunkHead(line);
      if (a === null) throw new Exit2(`error: parse ${i + 1}`);
      curHunk = { a, items: [] };
      i++;
    } else if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.isCreate = true;
      else if (line.startsWith('deleted file mode')) cur.isDelete = true;
      i++;
    } else {
      i++;
    }
  }
  flushBody();
  return sections.map((sec) => uniSectionEdit(sec, strict));
}

/** Apply one section's hunks to a file's text (section 6). */
function applyUniHunks(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  let f = fileLines(text);
  let d = 0;
  for (const hunk of hunks) {
    const o = hunk.items.filter((x) => x.kind === 'ctx' || x.kind === 'old').map((x) => x.text);
    if (o.length === 0) {
      const at = Math.min(hunk.a + d, f.lines.length);
      const n = applyBody(f.lines, hunk.items, at, 0);
      const nl = [...f.lines.slice(0, at), ...n, ...f.lines.slice(at)];
      let finalBreak = f.finalBreak;
      if (at === f.lines.length) finalBreak = !backslashAfterLast(hunk.items);
      f = { br: f.br, lines: nl, finalBreak };
      d += n.length;
      continue;
    }
    const found = findTier(f.lines, o, strict);
    if (found === null) throw new Fail('no-match', path);
    const target = hunk.a - 1 + d;
    let pos = found.positions[0]!;
    let best = Math.abs(pos - target);
    for (const p of found.positions) {
      const dist = Math.abs(p - target);
      if (dist < best) {
        best = dist;
        pos = p;
      }
    }
    const n = applyBody(f.lines, hunk.items, pos, found.tier);
    const nl = [...f.lines.slice(0, pos), ...n, ...f.lines.slice(pos + o.length)];
    let finalBreak = f.finalBreak;
    if (pos + o.length === f.lines.length) finalBreak = !backslashAfterLast(hunk.items);
    f = { br: f.br, lines: nl, finalBreak };
    d += n.length - o.length;
  }
  return writeLines(f);
}

function uniSectionEdit(sec: UniSection, strict: boolean): Edit {
  // null is /dev/null (a real value); undefined is unnamed. ?? would erase null, so check explicitly.
  const old = sec.pairOld !== undefined ? sec.pairOld : sec.renameFrom !== undefined ? sec.renameFrom : sec.gitOld;
  const nw = sec.pairNew !== undefined ? sec.pairNew : sec.renameTo !== undefined ? sec.renameTo : sec.gitNew;
  const isCreate = sec.isCreate || old === null;
  const isDelete = !isCreate && (sec.isDelete || nw === null);
  const isMove = !isCreate && !isDelete && old !== undefined && nw !== undefined && old !== null && nw !== null && old !== nw;
  return (tree) => {
    for (const p of [old, nw]) {
      if (p !== undefined && p !== null && !safe(p)) throw new Fail('unsafe', p);
    }
    if (isCreate) {
      if (nw === undefined || nw === null) return;
      if (tree.get(nw) !== null) throw new Fail('exists', nw);
      const plus: string[] = [];
      let lastBs = false;
      for (const hunk of sec.hunks) {
        for (let j = 0; j < hunk.items.length; j++) {
          if (hunk.items[j]!.kind === 'new') {
            plus.push(hunk.items[j]!.text);
            lastBs = hunk.items[j + 1]?.kind === 'bs';
          }
        }
      }
      tree.now.set(nw, plus.length === 0 ? '' : plus.join('\n') + (lastBs ? '' : '\n'));
      return;
    }
    if (isDelete) {
      if (old === undefined || old === null) throw new Fail('missing', '/dev/null');
      if (tree.get(old) === null) throw new Fail('missing', old);
      tree.now.set(old, null);
      return;
    }
    if (isMove) {
      const o = old as string;
      const n = nw as string;
      if (tree.get(o) === null) throw new Fail('missing', o);
      if (tree.get(n) !== null) throw new Fail('exists', n);
      const out = applyUniHunks(tree.get(o)!, sec.hunks, strict, o);
      tree.now.set(o, null);
      tree.now.set(n, out);
      tree.moves.push([o, n]);
      return;
    }
    const p = (old ?? nw) as string;
    if (tree.get(p) === null) throw new Fail('missing', p);
    tree.now.set(p, applyUniHunks(tree.get(p)!, sec.hunks, strict, p));
  };
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const isSearch = (l: string): boolean => l.trimEnd() === '<<<<<<< SEARCH';
  const isSep = (l: string): boolean => l.trimEnd() === '=======';
  const isReplace = (l: string): boolean => l.trimEnd() === '>>>>>>> REPLACE';
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | undefined;
  let i = 0;
  while (i < lines.length) {
    if (!isSearch(lines[i]!)) {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | undefined;
    for (let j = searchLine - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trimStart().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === undefined) {
      if (prevPath === undefined) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let sep = -1;
    for (let j = searchLine + 1; j < lines.length; j++) {
      if (isSep(lines[j]!)) {
        sep = j;
        break;
      }
      if (isReplace(lines[j]!)) break;
    }
    if (sep === -1) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = sep + 1; j < lines.length; j++) {
      if (isReplace(lines[j]!)) {
        rep = j;
        break;
      }
    }
    if (rep === -1) throw new Exit2(`error: parse ${searchLine + 1}`);
    edits.push(srBlockEdit(path, lines.slice(searchLine + 1, sep), lines.slice(sep + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

function srBlockEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    const f = fileLines(cur);
    const found = findTier(f.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const n = newLines.map((l) => reindentOne(l, oldLines[0]!, f.lines[pos]!, found.tier));
    f.lines = [...f.lines.slice(0, pos), ...n, ...f.lines.slice(pos + oldLines.length)];
    tree.now.set(path, writeLines(f));
  };
}

/** Section 8: a V4A chunk: an optional anchor, body lines, whether it is end-of-file anchored. */
interface V4aChunk {
  anchor: string | null;
  items: BodyItem[];
  eof: boolean;
}
function v4aBodyItem(line: string): BodyItem | null {
  if (line === '') return { kind: 'ctx', text: '', bare: true };
  const c = line[0]!;
  if (c === ' ') return { kind: 'ctx', text: line.slice(1) };
  if (c === '-') return { kind: 'old', text: line.slice(1) };
  if (c === '+') return { kind: 'new', text: line.slice(1) };
  return null;
}
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isSectionStart = (l: string): boolean => l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    if (!isSectionStart(line)) throw new Exit2(`error: parse ${i + 1}`);
    const startIdx = i;
    const kind = line.startsWith('*** Add File: ') ? 'add' : line.startsWith('*** Delete File: ') ? 'delete' : 'update';
    const path = line.slice(line.indexOf(': ') + 2).trim();
    i++;
    const raw: { text: string; idx: number }[] = [];
    while (i < last) {
      const l = lines[i]!;
      if (isSectionStart(l)) break;
      raw.push({ text: l, idx: i });
      i++;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    if (kind === 'add') {
      const fileLines: string[] = [];
      for (const r of raw) {
        if (r.text === '') fileLines.push('');
        else if (r.text.startsWith('+')) fileLines.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.idx + 1}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
    } else if (kind === 'delete') {
      if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.idx + 1}`);
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
    } else {
      let moveTo: string | undefined;
      let at = 0;
      if (raw.length > 0 && raw[0]!.text.startsWith('*** Move to: ')) {
        moveTo = raw[0]!.text.slice('*** Move to: '.length).trim();
        at = 1;
      }
      const chunks: V4aChunk[] = [];
      let curChunk: V4aChunk | null = null;
      for (let j = at; j < raw.length; j++) {
        const r = raw[j]!;
        if (r.text.startsWith('@@')) {
          curChunk = { anchor: r.text.slice(2).trim(), items: [], eof: false };
          chunks.push(curChunk);
        } else if (r.text === '*** End of File') {
          if (curChunk === null) throw new Exit2(`error: parse ${r.idx + 1}`);
          curChunk.eof = true;
          curChunk = null;
        } else if (r.text.startsWith('***')) {
          throw new Exit2(`error: parse ${r.idx + 1}`);
        } else {
          const it = v4aBodyItem(r.text);
          if (it === null) throw new Exit2(`error: parse ${r.idx + 1}`);
          if (curChunk === null) {
            if (chunks.length > 0) throw new Exit2(`error: parse ${r.idx + 1}`);
            curChunk = { anchor: null, items: [], eof: false };
            chunks.push(curChunk);
          }
          curChunk.items.push(it);
        }
      }
      if (chunks.length === 0 && moveTo === undefined) throw new Exit2(`error: parse ${startIdx + 1}`);
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
    }
  }
  return edits;
}

function findAnchorAt(lines: string[], anchor: string, cursor: number, strict: boolean): number | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    for (let i = cursor; i < lines.length; i++) {
      if (tierEq(lines[i]!, anchor, t)) return i;
    }
  }
  return null;
}
function findChunkOcc(lines: string[], o: string[], cursor: number, strict: boolean, eof: boolean): { tier: number; pos: number } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const ps = occurrences(lines, o, t).filter((p) => p >= cursor && (!eof || p + o.length === lines.length));
    if (ps.length > 0) return { tier: t, pos: ps[0]! };
  }
  return null;
}

function v4aUpdateEdit(path: string, moveTo: string | undefined, chunks: V4aChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== undefined && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (moveTo !== undefined && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const f = fileLines(cur);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null && chunk.anchor !== '') {
        const aPos = findAnchorAt(f.lines, chunk.anchor, cursor, strict);
        if (aPos === null) throw new Fail('no-match', path);
        cursor = aPos + 1;
      }
      const o = chunk.items.filter((x) => x.kind === 'ctx' || x.kind === 'old').map((x) => x.text);
      if (o.length === 0) {
        const at = chunk.eof ? f.lines.length : cursor;
        const n = applyBody(f.lines, chunk.items, at, 0);
        f.lines = [...f.lines.slice(0, at), ...n, ...f.lines.slice(at)];
        cursor = at + n.length;
        continue;
      }
      const found = findChunkOcc(f.lines, o, cursor, strict, chunk.eof);
      if (found === null) throw new Fail('no-match', path);
      const n = applyBody(f.lines, chunk.items, found.pos, found.tier);
      f.lines = [...f.lines.slice(0, found.pos), ...n, ...f.lines.slice(found.pos + o.length)];
      cursor = found.pos + n.length;
    }
    const out = writeLines(f);
    if (moveTo !== undefined) {
      tree.now.set(path, null);
      tree.now.set(moveTo, out);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, out);
    }
  };
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = 0;
      tree.moves.push(...beforeMoves);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: [string, string][] = [];
  const rDone = new Set<string>();
  for (const [old, nw] of tree.moves) {
    if (tree.original(old) !== null && tree.get(old) === null && tree.original(nw) === null && tree.get(nw) !== null) {
      rows.push([nw, `R ${old} -> ${nw}`]);
      rDone.add(old);
      rDone.add(nw);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (!rDone.has(p)) rows.push([p, `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`]);
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a[0]), Buffer.from(b[0])));
  const outLines = rows.map((r) => r[1]);
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
