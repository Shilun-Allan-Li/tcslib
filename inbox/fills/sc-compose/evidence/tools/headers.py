#!/usr/bin/env python3
"""Frozen-statement check of the prf-long fill (brief: *The frozen-statement rule*).

usage: headers.py REPO BASE_REV FILE...            (compare BASE_REV:FILE with the working tree)
       headers.py --pair BASE_PATH FINAL_PATH        (compare two files on disk; for the control)

For every declaration of the base file (theorem, lemma, def, abbrev, structure, inductive, class,
instance, example; private ones included) it extracts
* the lines that modify it from just above (`omit … in`, `include … in`, `set_option … in`,
  attributes on their own line) — compared byte for byte;
* the docstring before its `**Proof sketch` paragraph (the statement prose) — byte for byte;
* the header: from the keyword line (with attributes and modifiers) to the top-level `:=`, `|`
  (an equation line `| … =>`) or `where` that begins the proof or body — byte for byte;
* for a `def`, `abbrev`, `structure`, `inductive`, `class` or `instance`: the whole declaration,
  body included — byte for byte;
and checks that each base declaration is present in the final file, in the same relative order.
Output: one line per difference (`DIFF kind file name`) and per base declaration (`OK`), then
`RESULT n differences`."""
import re, subprocess, sys

KW = r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\b\s*([^\s:({\[]*)')
PRE = re.compile(r'^(omit|include|set_option)\b.*\bin\s*$|^@\[[^\]]*\]\s*$')
STOP = re.compile(r'^(/-|--|end\b|section\b|namespace\b|variable\b|open\b|attribute\b|omit\b|include\b|'
                  r'set_option\b|noncomputable section\b|#)')
OPEN, CLOSE = '([{⟨⦃', ')]}⟩⦄'


def header_end(text):
    """Index where the header ends: the first `:=` or ` where` at bracket depth 0, or the start
    of a line `| … =>` at depth 0."""
    depth, i, line_start = 0, 0, True
    while i < len(text):
        c = text[i]
        if line_start:
            m = re.match(r'[ \t]*\|[^\n]*=>', text[i:])
            if m and depth == 0:
                return i
        line_start = c == '\n'
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and text.startswith(':=', i):
            return i
        elif depth == 0 and re.match(r'\swhere\b', text[i:i + 7]):
            return i
        i += 1
    return len(text)


def decls(src):
    lines = src.split('\n')
    out, counts = [], {}
    for k, l in enumerate(lines):
        m = DECL.match(l)
        if not m:
            continue
        kind, name = m.group(1), m.group(2) or m.group(1)
        counts[name] = counts.get(name, 0) + 1
        key = name if counts[name] == 1 else f'{name}#{counts[name]}'
        # pre-lines and docstring above
        j = k - 1
        pre = []
        while j >= 0 and PRE.match(lines[j]):
            pre.insert(0, lines[j]); j -= 1
        doc = ''
        if j >= 0 and lines[j].rstrip().endswith('-/'):
            d = j
            while d >= 0 and not lines[d].lstrip().startswith('/--'):
                d -= 1
            doc = '\n'.join(lines[d:j + 1])
            # an `omit … in` may also sit above the docstring
            e = d - 1
            while e >= 0 and PRE.match(lines[e]):
                pre.insert(0, lines[e]); e -= 1
        prose = doc.split('**Proof sketch')[0]
        # the declaration's extent
        e = k + 1
        while e < len(lines) and not (DECL.match(lines[e]) or STOP.match(lines[e]) or
                                      PRE.match(lines[e])):
            e += 1
        while e > k + 1 and lines[e - 1].strip() == '':
            e -= 1
        whole = '\n'.join(lines[k:e])
        out.append(dict(key=key, kind=kind, pre='\n'.join(pre), prose=prose,
                        header=whole[:header_end(whole)], whole=whole, line=k + 1))
    return out


def compare(path, base_src, final_src):
    b, f = decls(base_src), decls(final_src)
    fm = {d['key']: d for d in f}
    diffs = []
    for d in b:
        g = fm.get(d['key'])
        if g is None:
            diffs.append(f'DIFF missing {path} {d["key"]}')
            continue
        bad = []
        for part in ('pre', 'prose', 'header'):
            if d[part] != g[part]:
                bad.append(part)
        if d['kind'] in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance') and \
                d['whole'] != g['whole']:
            bad.append('definition-body')
        if bad:
            diffs.append(f'DIFF {"+".join(bad)} {path} {d["key"]} (base line {d["line"]}, final line {g["line"]})')
        else:
            print(f'OK {path} {d["key"]} (base line {d["line"]}, final line {g["line"]})')
    order_b = [d['key'] for d in b]
    order_f = [d['key'] for d in f if d['key'] in set(order_b)]
    if order_b != [k for k in order_f]:
        diffs.append(f'DIFF order {path}')
    added = [d['key'] for d in f if d['key'] not in {x['key'] for x in b}]
    print(f'FILE {path}: base {len(b)} declarations, final {len(f)} '
          f'({len(added)} added); order {"kept" if order_b == order_f else "CHANGED"}')
    return diffs


if __name__ == '__main__':
    if sys.argv[1] == '--pair':
        diffs = compare(sys.argv[3], open(sys.argv[2]).read(), open(sys.argv[3]).read())
    else:
        repo, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
        diffs = []
        for p in files:
            base = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{p}'], capture_output=True,
                                  text=True, check=True).stdout
            diffs += compare(p, base, open(f'{repo}/{p}').read())
    for d in diffs:
        print(d)
    print(f'RESULT {len(diffs)} differences')
