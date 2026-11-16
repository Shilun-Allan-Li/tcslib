"""Frozen-statement check for the gsw-security owned files (run with python3 -I).

Usage: frozen_headers.py <base-file> <final-file> [<label>]

Splits each file into top-level items (docstring + declaration, or a command such as
`open`, `set_option`, `attribute`, `namespace`, `import`, the module docstring). For every
declaration present at base it checks, byte for byte:
  * targets (a `theorem` whose base body is `sorry`): the header (attributes, modifiers,
    keyword, name, binders and type, up to the `:=`/`where`/`|` that begins the proof) and
    the docstring up to `**Proof sketch.**`;
  * every other declaration (defs, readers, other theorems) and every base command
    (`attribute [simps ...]`, `open`, `set_option`, imports, module title): the whole item;
  * the relative order of the base declarations in the final file.
Additions (new auxiliary declarations, new imports) are listed, not counted as differences.
Prints the full diff of every difference and a summary line
`DIFFERENCES=<n> CHANGED=<c> REMOVED=<r> ORDER=<ok|BROKEN>`. Exit 0 iff n == 0.
"""
import difflib, re, sys

STARTERS = ('/--', '/-!', '@[', 'attribute ', 'theorem ', 'lemma ', 'def ', 'noncomputable ',
            'private ', 'protected ', 'abbrev ', 'structure ', 'instance ', 'open ', 'namespace ',
            'end ', 'set_option ', 'import ', 'section', 'variable ', 'class ', 'inductive ',
            '/-')
KEYWORDS = ('theorem', 'lemma', 'def', 'abbrev', 'structure', 'instance', 'class', 'inductive')

def items(text):
    """Top-level items; a chunk ends where a new top-level starter begins outside a comment.
    Trailing blank lines are layout and are dropped from each item before comparison."""
    lines = text.split('\n')
    out, cur, in_doc = [], [], False
    for line in lines:
        if not in_doc and line.startswith(STARTERS) and cur and not _pending_doc(cur):
            out.append('\n'.join(cur).rstrip('\n')); cur = []
        cur.append(line)
        if line.startswith('/-') and '-/' not in line[2:]:
            in_doc = True
        elif in_doc and '-/' in line:
            in_doc = False
    if cur:
        out.append('\n'.join(cur).rstrip('\n'))
    return [i for i in out if i.strip()]

def _pending_doc(cur):
    """A chunk made only of a declaration docstring (or attributes) waits for its declaration."""
    body = '\n'.join(cur).strip()
    if body.startswith('/--') and body.endswith('-/'):
        return True
    if re.fullmatch(r'(/--.*?-/\s*)?(@\[[^\]]*\]\s*)+', body, re.S):
        return True
    return False

def decl_info(item):
    """Return (name, docstring, header, body, is_decl) of an item."""
    doc = ''
    rest = item
    m = re.match(r'(/--.*?-/)\n', item, re.S)
    if m:
        doc, rest = m.group(1), item[m.end():]
    km = re.search(r'(?m)^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*('
                   + '|'.join(KEYWORDS) + r')\s+(\S+)', rest)
    if not km or rest.startswith(('attribute ', 'open ', 'set_option ', 'namespace ', 'end ',
                                  'import ')):
        return (None, doc, rest, '', False)
    name = km.group(2)
    # Header: up to the first `:=`, or a line-initial `where`/` where`, or a line-initial `|`.
    cands = [i for i in (rest.find(':='), _find_re(rest, r'\swhere\b'),
                         _find_re(rest, r'\n\s*\|')) if i >= 0]
    cut = min(cands) if cands else len(rest)
    return (name, doc, rest[:cut], rest[cut:], True)

def _find_re(s, pat):
    m = re.search(pat, s)
    return m.start() if m else -1

def statement_prose(doc):
    i = doc.find('**Proof sketch.**')
    return doc if i < 0 else doc[:i]

def is_target(body):
    return re.fullmatch(r':=\s*by\s*sorry\s*', body) is not None

def main():
    base_path, final_path = sys.argv[1], sys.argv[2]
    label = sys.argv[3] if len(sys.argv) > 3 else final_path
    base = items(open(base_path).read())
    final = items(open(final_path).read())
    binfo = [decl_info(i) for i in base]
    finfo = [decl_info(i) for i in final]
    fdecl = {}
    for idx, (n, d, h, b, isd) in enumerate(finfo):
        if isd:
            fdecl.setdefault(n, []).append(idx)
    fcmds = [final[i] for i, f in enumerate(finfo) if not f[4]]
    diffs, changed, removed, rows = [], 0, 0, []
    order = []
    for item, (n, d, h, b, isd) in zip(base, binfo):
        if not isd:
            if item in fcmds:
                rows.append(f'SAME      command  {item.splitlines()[0][:70]}')
            else:
                removed += 1
                rows.append(f'REMOVED   command  {item.splitlines()[0][:70]}')
                diffs.append((f'command {item.splitlines()[0][:70]}', item, ''))
            continue
        if n not in fdecl or len(fdecl[n]) != 1:
            removed += 1
            rows.append(f'REMOVED   decl     {n} (occurrences at final: {len(fdecl.get(n, []))})')
            diffs.append((f'decl {n}', item, ''))
            continue
        j = fdecl[n][0]
        order.append(j)
        fn, fd, fh, fb, _ = finfo[j]
        if is_target(b):
            ok_h, ok_d = (h == fh), (statement_prose(d) == statement_prose(fd))
            kind = 'target'
            if ok_h and ok_d:
                rows.append(f'SAME      target   {n} (header and statement prose; body '
                            f'{"unchanged" if b == fb else "replaced"})')
            else:
                changed += 1
                rows.append(f'CHANGED   target   {n} (header {"ok" if ok_h else "DIFFERS"}, '
                            f'prose {"ok" if ok_d else "DIFFERS"})')
                if not ok_h:
                    diffs.append((f'header {n}', h, fh))
                if not ok_d:
                    diffs.append((f'prose {n}', statement_prose(d), statement_prose(fd)))
        else:
            if item == final[j]:
                rows.append(f'SAME      whole    {n}')
            else:
                changed += 1
                rows.append(f'CHANGED   whole    {n}')
                diffs.append((f'whole {n}', item, final[j]))
    order_ok = order == sorted(order)
    bnames = {i[0] for i in binfo if i[4]}
    added = [f[0] for f in finfo if f[4] and f[0] not in bnames]
    added_cmds = [c.splitlines()[0][:70] for c in fcmds if c not in base]
    print(f'# frozen-statement check: {label}')
    print(f'# base={base_path}\n# final={final_path}')
    for r in rows:
        print(r)
    for a in added:
        print(f'ADDED     decl     {a}')
    for a in added_cmds:
        print(f'ADDED     command  {a}')
    for title, a, b in diffs:
        print(f'--- DIFF {title}')
        for line in difflib.unified_diff(a.split('\n'), b.split('\n'), 'base', 'final',
                                         lineterm=''):
            print(line)
    n = changed + removed + (0 if order_ok else 1)
    print(f'DIFFERENCES={n} CHANGED={changed} REMOVED={removed} '
          f'ORDER={"ok" if order_ok else "BROKEN"} ADDED_DECLS={len(added)} '
          f'ADDED_COMMANDS={len(added_cmds)}')
    sys.exit(0 if n == 0 else 1)

if __name__ == '__main__':
    main()
