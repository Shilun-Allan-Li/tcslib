#!/usr/bin/env python3
"""C8 sizes and C9 hygiene for the owned file. Usage: python3 -I sizes_hygiene.py <repo> <base> <head>
C8: lines and maximum width (Python len) at base and head. C9: every declaration added at the head
(helpers; U13 adds none) without a docstring stating a formula (a backticked span) or "Glue.", and
every proof of 20 lines or more whose docstring has no `**Proof sketch.**`."""
import sys, re, subprocess
repo, base, head = sys.argv[1:4]
F = 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean'
def show(r): return subprocess.run(['git', '-C', repo, 'show', f'{r}:{F}'], capture_output=True, text=True, check=True).stdout
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance)\s+([^\s(:{\[]+)')
def decls(t):
    L = t.split('\n'); out = []
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m: continue
        j = i - 1; doc = []
        if j >= 0 and L[j].rstrip().endswith('-/'):
            k = j
            while '/--' not in L[k]: k -= 1
            doc = L[k:j + 1]
        k = i
        while k < len(L) and not re.search(r':=( by)?\s*$|:= rfl|:=\s*\S', L[k]): k += 1
        e = k + 1
        while e < len(L) and L[e].strip() and not DECL.match(L[e]) and not L[e].startswith('/--'): e += 1
        out.append((m.group(2), i + 1, '\n'.join(doc), e - k - 1))
    return out
for r, name in ((base, 'base'), (head, 'head')):
    t = show(r); L = t.rstrip('\n').split('\n')
    print(f'C8 {name} {r}: {len(L)} lines, max width {max(len(l) for l in L)}, lines over 100: '
          f'{sum(1 for l in L if len(l) > 100)}')
b = {n for n, *_ in decls(show(base))}
issues = 0
for n, line, doc, plen in decls(show(head)):
    new = n not in b
    if new and not (re.search(r'`[^`]+`', doc) or 'Glue.' in doc):
        print(f'C9 helper without formula or Glue.: {n} (line {line})'); issues += 1
    if plen >= 20 and '**Proof sketch.**' not in doc:
        print(f'C9 proof of {plen} lines without a sketch: {n} (line {line})'); issues += 1
    print(f'  {"NEW " if new else ""}{n} (line {line}): proof {plen} lines, sketch {"yes" if "**Proof sketch.**" in doc else "no"}')
print(f'C9 RESULT: {issues} finding(s)')
