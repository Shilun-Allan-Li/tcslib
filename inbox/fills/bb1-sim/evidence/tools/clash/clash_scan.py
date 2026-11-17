"""(bb1-sim, lead: copied unchanged from bb1-sim-statements, which copied it unchanged from bb1-machine.)
clash_scan.py <repo> <base-rev> <head-rev> <out-dir-or-tsv>

Name-clash scan of fill bb1-machine (brief: "Checks and report" -> "Name-clash scan"). Run as
`python3 -I clash_scan.py ...`. Reads git objects only (`git diff`, `git ls-tree -r`,
`git cat-file --batch`), never the working tree; runs no Lean.

1. New declarations: every declaration whose header line is added between <base-rev> and
   <head-rev> in a `TCSlib/**/*.lean` file (new files: every line; changed files: the `+` lines of
   `git diff -U0`). Kinds: theorem, lemma, def, abbrev, instance (named only), structure,
   inductive, class (incl. `class inductive`), opaque, axiom, alias, irreducible_def; with the
   modifiers private / protected / noncomputable / partial / unsafe / nonrec / scoped / local
   recorded as flags. Only lines outside comments and strings count, whose first token is the
   command (indentation allowed: one base file indents a `lemma`).
2. Full names are resolved from the enclosing `namespace X.Y` / `section [S]` / `mutual` /
   `end [..]` blocks (a dotted namespace contributes all its components; `end X.Y` closes it),
   and a dotted declaration name `Foo.bar` inside namespace `N` resolves to `N.Foo.bar`;
   `_root_.` is honoured.
3. Base index: every `.lean` file of `TCSlib/` and `audits/` at <base-rev> is parsed the same way.
   A new name is CLASH if a declaration with the same resolved full name exists at <base-rev> in
   another file, or in the same file when the head file holds more declarations of that name than
   the base file (otherwise a declaration whose full name already exists in the same file at
   <base-rev> is classified MODIFIED: a changed header line of an existing declaration, not a new
   name). Two new declarations with the same full name
   are DUP-NEW. Same-short-name (last component) declarations elsewhere are listed as INFO.
Private names are compared like public ones (the brief: "public or private, namespaces resolved").
Not covered (stated, not checked): auto-generated names (structure fields/`mk`, inductive
constructors, `simps`/`to_additive`/equation lemmas), declarations produced by macros.

Output: <out>/clash.tsv (or <out> itself when it ends in .tsv) with columns
status, full_name, kind, flags, head_location, clash_locations, info_same_short_name; and a
summary printed and appended as `RESULT: <n> new names, <k> clashes` (exit 0 iff k == 0 and no
DUP-NEW).

The core is importable: `parse_decls(text)` -> declarations, `base_index(repo, rev)` -> index,
`added_decls(text, added_lines, path)` -> new declarations of a (synthetic) head file,
`classify(new_decls, index)` -> rows (used by clash_controls.py).

written by tools-agent (sub-agent), fill bb1-machine
"""
import os
import re
import subprocess
import sys

KINDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'inductive', 'class',
         'opaque', 'axiom', 'alias', 'irreducible_def')
MODS = ('private', 'protected', 'noncomputable', 'partial', 'unsafe', 'nonrec', 'scoped', 'local')
ATTR = r'(?:@\[(?:[^\[\]]|\[[^\[\]]*\])*\]\s*)*'
DECL_RE = re.compile(r'^' + ATTR + r'((?:(?:' + '|'.join(MODS) + r')\s+)*)'
                     r'(class\s+inductive|' + '|'.join(KINDS) + r')\b(.*)$')
NAME_RE = re.compile(r'\s*((?:«[^»]*»|[^\s:({\[⦃«.]+)(?:\.(?:«[^»]*»|[^\s:({\[⦃«.]+))*)')


def strip_code(text):
    """Return the lines of `text` with comments and string literals blanked (same line count)."""
    out, cur = [], []
    depth = 0
    i, n = 0, len(text)
    instr = False
    while i < n:
        c = text[i]
        if c == '\n':
            out.append(''.join(cur))
            cur = []
            i += 1
            continue
        if depth > 0:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
            cur.append(' ')
            continue
        if instr:
            if c == '\\':
                i += 2
                cur.append('  ')
                continue
            if c == '"':
                instr = False
            cur.append(' ')
            i += 1
            continue
        if text.startswith('/-', i):
            depth = 1
            i += 2
            cur.append('  ')
            continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            cur.append(' ' * (j - i))
            i = j
            continue
        if c == '"':
            instr = True
            cur.append(' ')
            i += 1
            continue
        if c == "'" and i + 2 < n and text[i + 2] == "'" and text[i + 1] != '\n':
            cur.append("' '")  # char literal 'x'
            i += 3
            continue
        cur.append(c)
        i += 1
    out.append(''.join(cur))
    return out


def parse_decls(text):
    """Declarations of a Lean file: list of dicts (full, short, kind, flags, line)."""
    lines = strip_code(text)
    stack = []  # entries: (kind, [components])
    decls = []
    for ln, code in enumerate(lines, 1):
        code = code.strip()  # commands may be indented (e.g. QuantumSingleton.lean)
        tok = code.split()
        if not tok:
            continue
        if tok[0] == 'namespace' and len(tok) > 1:
            stack.append(('namespace', tok[1].split('.')))
            continue
        if tok[0] == 'section' or tok[:2] == ['noncomputable', 'section'] or \
                tok[:2] == ['public', 'section']:
            stack.append(('section', []))
            continue
        if tok[0] == 'mutual':
            stack.append(('mutual', []))
            continue
        if tok[0] == 'end':
            # `end A.B` closes `namespace A.B`; `end B` closes only the last component of it
            k = len(tok[1].split('.')) if len(tok) > 1 else 0
            if stack and stack[-1][0] == 'namespace' and 0 < k < len(stack[-1][1]):
                stack[-1] = ('namespace', stack[-1][1][:-k])
            elif stack:
                stack.pop()
            continue
        m = DECL_RE.match(code)
        if not m:
            continue
        mods, kind, rest = m.group(1).split(), re.sub(r'\s+', ' ', m.group(2)), m.group(3)
        if kind == 'instance':
            rest = re.sub(r'^\s*\(priority\s*:=[^)]*\)', '', rest)
        nm = NAME_RE.match(rest)
        if not nm or not nm.group(1) or nm.group(1).startswith('⟨'):
            continue  # anonymous instance or unparsable
        name = nm.group(1)
        if kind == 'instance' and (rest.lstrip().startswith(('[', '(', '{', ':', '⦃'))):
            continue  # anonymous instance with binders
        if name.startswith('_root_.'):
            full = name[len('_root_.'):]
        else:
            ns = [c for k, comps in stack if k == 'namespace' for c in comps]
            full = '.'.join(ns + [name])
        decls.append(dict(full=full, short=full.split('.')[-1], kind=kind, flags=mods,
                          line=ln))
    return decls


def git(repo, *args, inp=None):
    r = subprocess.run(['git', '-C', repo] + list(args), input=inp, capture_output=True,
                       check=True)
    return r.stdout


def cat_files(repo, rev, paths):
    """Contents of `paths` at `rev` via one `git cat-file --batch` call."""
    if not paths:
        return {}
    inp = ''.join(f'{rev}:{p}\n' for p in paths).encode('utf-8')
    data = git(repo, 'cat-file', '--batch', inp=inp)
    res, pos = {}, 0
    for p in paths:
        nl = data.index(b'\n', pos)
        hdr = data[pos:nl].split()
        if len(hdr) < 3 or hdr[1] != b'blob':
            raise RuntimeError(f'cat-file failed for {rev}:{p}: {data[pos:nl]!r}')
        size = int(hdr[2])
        res[p] = data[nl + 1:nl + 1 + size].decode('utf-8')
        pos = nl + 1 + size + 1
    return res


def base_index(repo, rev, roots=('TCSlib', 'audits')):
    paths = [p for p in git(repo, 'ls-tree', '-r', '--name-only', rev, '--', *roots)
             .decode('utf-8').splitlines() if p.endswith('.lean')]
    texts = cat_files(repo, rev, paths)
    full, short = {}, {}
    for p in paths:
        for d in parse_decls(texts[p]):
            loc = dict(d, path=p)
            full.setdefault(d['full'], []).append(loc)
            short.setdefault(d['short'], []).append(loc)
    return dict(full=full, short=short, nfiles=len(paths),
                ndecls=sum(len(v) for v in full.values()))


def new_decls(repo, base, head):
    st = git(repo, 'diff', '--no-renames', '--name-status', base, head, '--', 'TCSlib') \
        .decode('utf-8').splitlines()
    files = [(s.split('\t')[0], s.split('\t')[1]) for s in st]
    files = [(k, p) for k, p in files if p.endswith('.lean') and k in ('A', 'M')]
    texts = cat_files(repo, head, [p for _, p in files])
    out = []
    for k, p in files:
        if k == 'A':
            added = None
        else:
            added = set()
            diff = git(repo, 'diff', '-U0', '--no-renames', base, head, '--', p).decode('utf-8')
            for h in re.finditer(r'^@@ -\S+ \+(\d+)(?:,(\d+))? @@', diff, re.M):
                s, c = int(h.group(1)), int(h.group(2) or '1')
                added.update(range(s, s + c))
        out += added_decls(texts[p], added, p, k)
    return out, files


def added_decls(text, added, path, status_file='M'):
    """Declarations of `text` (the head version of `path`) whose header line is in `added`
    (None: every line), each with `head_count`, its full name's multiplicity in the head file."""
    decls = parse_decls(text)
    cnt = {}
    for d in decls:
        cnt[d['full']] = cnt.get(d['full'], 0) + 1
    return [dict(d, path=path, status_file=status_file, head_count=cnt[d['full']])
            for d in decls if added is None or d['line'] in added]


def classify(news, index):
    rows = []
    seen = {}
    for d in news:
        seen.setdefault(d['full'], []).append(d)
    for d in news:
        same = index['full'].get(d['full'], [])
        here = [x for x in same if x['path'] == d['path']]
        other = [x for x in same if x['path'] != d['path']]
        if here and not other and d.get('head_count', 1) <= len(here):
            st = 'MODIFIED'
        elif same:
            st = 'CLASH'
        elif len(seen[d['full']]) > 1:
            st = 'DUP-NEW'
        else:
            st = 'OK'
        info = [x for x in index['short'].get(d['short'], []) if x['full'] != d['full']]
        rows.append(dict(d, status=st, clash=same, info=info))
    return rows


def fmt_locs(locs, limit=12):
    s = ', '.join(f'{x["path"]}:{x["line"]} {x["full"]}' + (' [private]' if 'private' in
                  x['flags'] else '') for x in locs[:limit])
    return s + (f', ... (+{len(locs) - limit})' if len(locs) > limit else '')


def write_report(rows, out_tsv, header_lines):
    with open(out_tsv, 'w', encoding='utf-8') as fh:
        for h in header_lines:
            fh.write('# ' + h + '\n')
        fh.write('status\tfull_name\tkind\tflags\thead_location\tclash_locations\t'
                 'info_same_short_name\n')
        for r in rows:
            fh.write('\t'.join([r['status'], r['full'], r['kind'], ' '.join(r['flags']) or '-',
                                f'{r["path"]}:{r["line"]}', fmt_locs(r['clash']) or '-',
                                (f'{len(r["info"])}: ' + fmt_locs(r['info'], 6))
                                if r['info'] else '-']) + '\n')
        new = [r for r in rows if r['status'] != 'MODIFIED']
        k = sum(r['status'] == 'CLASH' for r in rows)
        dup = sum(r['status'] == 'DUP-NEW' for r in rows)
        res = f'RESULT: {len(new)} new names, {k} clashes'
        fh.write(f'# MODIFIED (existing declarations with changed header lines, not new): '
                 f'{sum(r["status"] == "MODIFIED" for r in rows)}; DUP-NEW: {dup}\n')
        fh.write(res + '\n')
    return res, k, dup


def main(argv):
    if len(argv) != 5:
        print(__doc__)
        return 2
    repo, base, head, out = argv[1:5]
    base_c = git(repo, 'rev-parse', base + '^{commit}').decode().strip()
    head_c = git(repo, 'rev-parse', head + '^{commit}').decode().strip()
    out_tsv = out if out.endswith('.tsv') else os.path.join(out, 'clash.tsv')
    os.makedirs(os.path.dirname(os.path.abspath(out_tsv)), exist_ok=True)
    news, files = new_decls(repo, base_c, head_c)
    index = base_index(repo, base_c)
    rows = classify(news, index)
    hdr = [f'clash_scan.py repo={repo} base={base_c} head={head_c}',
           f'changed TCSlib .lean files (A/M): {len(files)}: '
           + ' '.join(f'{k}:{p}' for k, p in files),
           f'base index: {index["nfiles"]} .lean files under TCSlib/ and audits/, '
           f'{index["ndecls"]} declarations, {len(index["full"])} distinct full names',
           f'new declarations parsed: {len(news)} (private: '
           f'{sum("private" in d["flags"] for d in news)})']
    res, k, dup = write_report(rows, out_tsv, hdr)
    for h in hdr:
        print(h)
    for r in rows:
        if r['status'] != 'OK':
            print(f'{r["status"]}\t{r["full"]}\t{r["path"]}:{r["line"]}\t{fmt_locs(r["clash"])}')
    print(f'status counts: ' + ', '.join(f'{s} {sum(r["status"] == s for r in rows)}'
                                         for s in ('OK', 'CLASH', 'DUP-NEW', 'MODIFIED')))
    print(f'rows with same-short-name INFO: {sum(bool(r["info"]) for r in rows)}')
    print(f'output: {out_tsv}')
    print(res)
    return 0 if k == 0 and dup == 0 else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
