"""Owned-region check for UniversalK.lean (U2-S cont1): base vs head.
usage: python3 -I regions_u2s.py <base file> <head file>"""
import sys, difflib
b = open(sys.argv[1], encoding='utf-8').read().split('\n')
h = open(sys.argv[2], encoding='utf-8').read().split('\n')
sm = difflib.SequenceMatcher(a=b, b=h, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
HOME0 = b.index('/-! ## U2-S: the startup -/') + 1          # 1-based line of the marker
DOC0 = next(i for i, l in enumerate(b) if l.startswith('/-- **U2-S, the `k`-generic startup**')) + 1
SORRY = next(i for i in range(DOC0, len(b)) if b[i] == '  sorry') + 1
print(f'base markers: home marker line {HOME0}; target docstring line {DOC0}; target sorry line {SORRY}')
def region(tag, i1, i2):
    # i1,i2: 0-based half-open base range replaced (insert: i1 == i2, insertion before base line i1+1)
    if tag == 'insert' and i1 == 10: return '(a) import after base line 10'
    if HOME0 <= i1 and i2 <= DOC0 - 1 and (tag != 'insert' or i1 >= HOME0): return '(b) home (base lines %d..%d)' % (HOME0 + 1, DOC0 - 1)
    if i1 == SORRY - 1 and i2 == SORRY: return '(c) target body'
    return 'OUTSIDE'
ok = True
for tag, i1, i2, j1, j2 in ops:
    r = region(tag, i1, i2)
    ok &= r != 'OUTSIDE'
    print(f'{tag}: base {i1+1}..{i2} ({i2-i1}) -> head {j1+1}..{j2} ({j2-j1})  {r}')
    if tag == 'insert' and i1 == 10: print('   inserted:', h[j1:j2])
print('all hunks in regions (a)-(c):', ok, '; hunks:', len(ops))
# frozen spans byte-equal
def span(lines, a, z): return '\n'.join(lines[a:z])
hd = next(i for i, l in enumerate(h) if l.startswith('/-- **U2-S, the `k`-generic startup**'))
hs = next(i for i in range(hd, len(h)) if h[i].strip() == 'R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by')
bs = next(i for i in range(DOC0 - 1, len(b)) if b[i].strip() == 'R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by')
print('target docstring + statement byte-equal (base %d..%d, head %d..%d):' % (DOC0, bs + 1, hd + 1, hs + 1), span(b, DOC0 - 1, bs + 1) == span(h, hd, hs + 1))
print('module header (base 1..%d) = head minus the import:' % HOME0, b[:HOME0] == h[:10] + h[11:HOME0 + 1])
bt = b.index('/-! ## U2-U: the self-application universal machine -/'); ht = h.index('/-! ## U2-U: the self-application universal machine -/')
print('tail from U2-U marker byte-equal (base %d.., head %d..):' % (bt + 1, ht + 1), b[bt:] == h[ht:])
print('head: target body lines %d..%d; blank then U2-U marker at %d' % (hs + 2, ht - 1, ht + 1))
# docstring "Implementation status" present?
print('Implementation status paragraphs in head:', sum('**Implementation status.**' in l for l in h))
