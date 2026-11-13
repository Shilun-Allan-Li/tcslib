#!/usr/bin/env python3
"""bodies.py <root> <base-rev> <file>...: the complement of decls2.py.

For every declaration of the given files, private ones included, compare base and working tree:
  * a definition-like declaration (def, abbrev, instance, structure, inductive, class): its whole
    text (header and body), whitespace-normalized, comments removed;
  * a private theorem or lemma: its header (up to the top-level `:=`), as decls2 does for public
    ones.
Declarations are keyed by (visibility, full name). Prints TSV rows
  CHANGED-BODY / CHANGED-PRIVATE-HEADER / ADDED / REMOVED, with the normalized texts for changes.
Public theorem headers are decls2's job and are not repeated here.
"""
import re
import subprocess
import sys

root, base = sys.argv[1], sys.argv[2]
files = sys.argv[3:]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class)'
STOP = re.compile(r'^(/--|/-!|@\[|attribute\b|section\b|end\b|namespace\b|open\b|variable\b|'
                  r'set_option\b|#|example\b|theorem\b|lemma\b|def\b|abbrev\b|structure\b|'
                  r'inductive\b|instance\b|class\b|private\b|protected\b|noncomputable\b|nonrec\b)')


def strip(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)


def cut(t):
    d = 0
    for k, ch in enumerate(t):
        if ch in '([{⟨':
            d += 1
        elif ch in ')]}⟩':
            d -= 1
        elif d == 0 and t.startswith(':=', k):
            return t[:k]
    return t


def decls(src):
    lines = strip(src).split('\n')
    out, ns, i = {}, [], 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            ns.append(m.group(1)); i += 1; continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); i += 1; continue
        m = re.match(r'^(@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*' + KW +
                     r'\s+([^\s(:{\[]+)', l)
        if m:
            kind, name = m.group(3), m.group(4)
            priv = bool(re.search(r'\bprivate\b', l.split(name)[0]))
            full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns + [name])
            j = i + 1
            while j < len(lines) and not (lines[j] and not lines[j][0].isspace() and STOP.match(lines[j])):
                j += 1
            text = re.sub(r'\s+', ' ', ' '.join(lines[i:j])).strip()
            text = re.sub(r'^@\[[^\]]*\]\s*', '', text)
            out[('private' if priv else 'public', full)] = (kind, i + 1, text)
            i = j
            continue
        i += 1
    return out


for f in files:
    old = subprocess.run(['git', 'show', f'{base}:{f}'], cwd=root, capture_output=True,
                         text=True).stdout
    new = open(f'{root}/{f}', encoding='utf-8').read()
    a, b = decls(old) if old else {}, decls(new)
    for key in sorted(set(a) | set(b)):
        vis, n = key
        if key in a and key not in b:
            print(f"REMOVED\t{f}:{a[key][1]}\t{vis}\t{n}\t{a[key][0]}")
        elif key in b and key not in a:
            print(f"ADDED\t{f}:{b[key][1]}\t{vis}\t{n}\t{b[key][0]}")
        else:
            ka, la, ta = a[key]
            kb, lb, tb = b[key]
            if ka in ('theorem', 'lemma'):
                if vis == 'private' and cut(ta) != cut(tb):
                    print(f"CHANGED-PRIVATE-HEADER\t{f}:{lb}\t{vis}\t{n}\t{kb}\n  base: {cut(ta)}\n  head: {cut(tb)}")
            elif ta != tb:
                print(f"CHANGED-BODY\t{f}:{lb}\t{vis}\t{n}\t{kb}\n  base: {ta}\n  head: {tb}")
