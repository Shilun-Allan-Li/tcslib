"""Frozen-statement check for the gsw-core fill (python3 -I).

For each owned file, compare the issue base with the final text:
  * every declaration of the base is still present, in the same order (new auxiliary
    declarations may be interleaved);
  * the header of every base declaration (modifiers, attributes, keyword, name, binders and
    type, up to the top-level `:=`, `where` or first `|` that begins the proof) is
    byte-identical, including any `open … in` / `include … in` / `omit … in` prefix;
  * every base declaration whose body is not exactly `by sorry` (definitions, abbrevs,
    structures, instances, readers) is byte-identical as a whole, docstring included;
  * for the targets (body `by sorry` at base), the docstring prose before `**Proof sketch.**`
    is byte-identical;
  * every non-declaration command of the base (`import`, `set_option`, `namespace`, `section`,
    `end`, `variable`, `open`, module docstring) is still present, in order (the module
    docstring may differ only by added lines; new `import` lines may be added).
Prints the full diff of every changed item and a verdict line.

usage: headers.py BASE_REV ROOT FILE... [--final-rev REV]
       headers.py --controls BASE_REV ROOT FILE   (runs the two controls on FILE)
"""
import difflib, re, subprocess, sys
from pathlib import Path

DECL_KW = r'(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)'
MODS = r'(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)*' + MODS + DECL_KW + r'\b')
PREFIX_RE = re.compile(r'^(?:open|include|omit)\b.*\bin\s*$')
CMD_RE = re.compile(r'^(import|set_option|namespace|section|end|variable|open|universe|'
                    r'attribute|noncomputable section)\b')


def items(src):
    """Split a Lean file into top-level items (docstring + declaration kept together)."""
    lines = src.splitlines(keepends=True)
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('/-!') or (line.startswith('/-') and not line.startswith('/--')):
            j = i
            while '-/' not in lines[j]:
                j += 1
            out.append(('moddoc' if line.startswith('/-!') else 'comment', ''.join(lines[i:j + 1])))
            i = j + 1
            continue
        if line.strip() == '':
            i += 1
            continue
        start = i
        if line.startswith('/--'):
            j = i
            while '-/' not in lines[j]:
                j += 1
            i = j + 1
        while i < len(lines) and PREFIX_RE.match(lines[i]):
            i += 1
        if i < len(lines) and (DECL_RE.match(lines[i]) or lines[i].startswith('@[')):
            j = i + 1
            while j < len(lines) and (lines[j].startswith((' ', '\t')) or lines[j].strip() == ''
                                      or lines[j].startswith('|')):
                j += 1
            while j > i + 1 and lines[j - 1].strip() == '':
                j -= 1
            out.append(('decl', ''.join(lines[start:j])))
            i = j
            continue
        if CMD_RE.match(lines[start]):
            j = start + 1
            while j < len(lines) and lines[j].startswith((' ', '\t')):
                j += 1
            out.append(('cmd', ''.join(lines[start:j])))
            i = j
            continue
        out.append(('other', lines[start]))
        i = start + 1
    return out


def split_decl(text):
    """Return (docstring, header, body, name) of a declaration item."""
    doc = ''
    if text.startswith('/--'):
        k = text.index('-/') + 2
        doc, text = text[:k], text[k:].lstrip('\n')
    m = re.search(DECL_KW + r'\s+([^\s(\[{:]+)', text)
    name = m.group(1) if m else '?'
    depth, k = 0, 0
    while k < len(text):
        c = text[k]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and text.startswith(':=', k):
            break
        elif depth == 0 and re.match(r'\swhere\b', text[k:]):
            break
        elif depth == 0 and text.startswith('\n|', k):
            break
        k += 1
    return doc, text[:k], text[k:], name


def show(rev, root, path):
    if rev is None:
        return (Path(root) / path).read_text()
    return subprocess.check_output(['git', '-C', root, 'show', f'{rev}:{path}'], text=True)


def compare(base_src, final_src, path):
    diffs, notes = [], []
    b_items, f_items = items(base_src), items(final_src)
    b_decls = [split_decl(t) + (t,) for k, t in b_items if k == 'decl']
    f_decls = [split_decl(t) + (t,) for k, t in f_items if k == 'decl']
    f_names = [d[3] for d in f_decls]
    pos = -1
    for doc, head, body, name, whole in b_decls:
        if name not in f_names:
            diffs.append(f'{path}: REMOVED declaration {name}')
            continue
        idx = f_names.index(name)
        if idx < pos:
            diffs.append(f'{path}: ORDER changed at {name}')
        pos = max(pos, idx)
        fdoc, fhead, fbody, _, fwhole = f_decls[idx]
        if head != fhead:
            diffs.append(f'{path}: HEADER differs for {name}\n' + ''.join(difflib.unified_diff(
                head.splitlines(True), fhead.splitlines(True), 'base', 'final')))
        is_target = re.fullmatch(r':=\s*by\s+sorry\s*', body) is not None
        if not is_target:
            if head == fhead and whole != fwhole:
                diffs.append(f'{path}: WHOLE declaration differs for {name}\n' +
                             ''.join(difflib.unified_diff(whole.splitlines(True),
                                                          fwhole.splitlines(True), 'base', 'final')))
        else:
            cut = '**Proof sketch.**'
            bp = doc.split(cut)[0] if cut in doc else doc[:-2]
            fp = fdoc.split(cut)[0] if cut in fdoc else fdoc[:-2]
            if bp != fp:
                diffs.append(f'{path}: STATEMENT PROSE differs for {name}\n' +
                             ''.join(difflib.unified_diff(bp.splitlines(True), fp.splitlines(True),
                                                          'base', 'final')))
            elif doc != fdoc:
                notes.append(f'{path}: sketch edited for {name}\n' + ''.join(difflib.unified_diff(
                    doc.splitlines(True), fdoc.splitlines(True), 'base', 'final')))
            notes.append(f'{path}: target {name}: body replaced ({len(body.splitlines())} -> '
                         f'{len(fbody.splitlines())} lines)')
    # non-declaration commands, in order
    b_cmds = [t for k, t in b_items if k in ('cmd', 'comment')]
    f_cmds = [t for k, t in f_items if k in ('cmd', 'comment')]
    it = iter(f_cmds)
    for c in b_cmds:
        if not any(c == x for x in it):
            diffs.append(f'{path}: COMMAND missing or reordered: {c.strip()}')
    for c in f_cmds:
        if c not in b_cmds:
            if c.startswith('import '):
                notes.append(f'{path}: added import {c.strip()}')
            else:
                diffs.append(f'{path}: COMMAND added: {c.strip()}')
    b_md = [t for k, t in b_items if k == 'moddoc']
    f_md = [t for k, t in f_items if k == 'moddoc']
    if len(b_md) != len(f_md):
        diffs.append(f'{path}: module docstring count {len(b_md)} -> {len(f_md)}')
    for bm, fm in zip(b_md, f_md):
        sm = difflib.SequenceMatcher(a=bm.splitlines(True), b=fm.splitlines(True))
        ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
        if any(o[0] != 'insert' for o in ops):
            diffs.append(f'{path}: MODULE DOCSTRING changed beyond additions\n' +
                         ''.join(difflib.unified_diff(bm.splitlines(True), fm.splitlines(True))))
        elif ops:
            notes.append(f'{path}: module docstring additions\n' + ''.join(
                difflib.unified_diff(bm.splitlines(True), fm.splitlines(True), 'base', 'final')))
    new = [d[3] for d in f_decls if d[3] not in [b[3] for b in b_decls]]
    if new:
        notes.append(f'{path}: new declarations: {", ".join(new)}')
    others = [t for k, t in b_items if k == 'other']
    if others:
        notes.append(f'{path}: unclassified base lines: {others}')
    return diffs, notes, len(b_decls)


def main(argv):
    if argv[0] == '--controls':
        base, root, path = argv[1:4]
        src = show(base, root, path)
        ok = True
        # Control 1: one header altered by one character must give exactly one difference.
        # The altered character is the first `P` of the type of the first target (a theorem
        # whose body is `by sorry`), turned into `Q`.
        tgt = next(t for k, t in items(src) if k == 'decl' and
                   re.fullmatch(r':=\s*by\s+sorry\s*', split_decl(t)[2]))
        doc, head, _, tname = split_decl(tgt)
        colon = head.index(') :') + 3 if ') :' in head else head.index(' :') + 2
        k = head.index('P', colon)
        newhead = head[:k] + 'Q' + head[k + 1:]
        altered = src.replace(tgt, tgt.replace(head, newhead, 1), 1)
        d1, _, _ = compare(src, altered, path)
        print(f'CONTROL header-1-char on {path} ({tname}): {len(d1)} difference(s)')
        for d in d1:
            print('   ' + d.splitlines()[0])
        ok &= len(d1) == 1 and 'HEADER differs' in d1[0]
        # Control 2: a deleted reader must report exactly one removal.
        its = items(src)
        reader = next(t for k, t in its if k == 'decl' and
                      re.search(r'theorem \S*_(?:eq|apply|iff)\b', t))
        deleted = src.replace(reader, '', 1)
        d2, _, _ = compare(src, deleted, path)
        print(f'CONTROL deleted-reader on {path} ({split_decl(reader)[3]}): {len(d2)} difference(s)')
        for d in d2:
            print('   ' + d.splitlines()[0])
        ok &= len(d2) == 1 and 'REMOVED' in d2[0]
        print('CONTROLS ' + ('PASS' if ok else 'FAIL'))
        return 0 if ok else 1
    base, root, files = argv[0], argv[1], [a for a in argv[2:] if not a.startswith('--')]
    final_rev = argv[argv.index('--final-rev') + 1] if '--final-rev' in argv else None
    if final_rev:
        files = [f for f in files if f != final_rev]
    total = 0
    for path in files:
        diffs, notes, n = compare(show(base, root, path), show(final_rev, root, path), path)
        print(f'== {path}: {n} base declarations, {len(diffs)} unexpected difference(s)')
        for d in diffs:
            print('DIFF ' + d)
        for nt in notes:
            print('NOTE ' + nt)
        total += len(diffs)
    print(f'HEADERS {"PASS" if total == 0 else "FAIL"}: {total} unexpected difference(s)')
    return 0 if total == 0 else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
