"""Direct comparison of the frozen spans, base vs a later version, located by anchors (python3 -I).
usage: python3 -I frozen_cmp.py <base> <later>"""
import sys
A = open(sys.argv[1], encoding='utf-8').read().split('\n'); B = open(sys.argv[2], encoding='utf-8').read().split('\n')
def find(L, pref):
    k = [i for i, l in enumerate(L) if l.startswith(pref)]
    assert len(k) == 1, (pref, k); return k[0]
a_doc = find(A, '/-- **The stage query in linear time**'); b_doc = find(B, '/-- **The stage query in linear time**')
a_d = find(A, '**Implementation status.**'); b_d = find(B, '**Implementation status.**')
a_t = find(A, 'theorem exists_queryTM'); b_t = find(B, 'theorem exists_queryTM')
a_x = find(A, '/-- **The diagonalizer**'); b_x = find(B, '/-- **The diagonalizer**')
print(f'base lines {len(A) - 1}; later lines {len(B) - 1}; target docstring base {a_doc + 1} / later {b_doc + 1}')
def cmp(name, a1, a2, b1):
    eq = A[a1:a2] == B[b1:b1 + (a2 - a1)]
    diff = [a1 + i + 1 for i in range(a2 - a1) if A[a1 + i] != B[b1 + i]]
    print(f'{"EQUAL  " if eq else "DIFFERS"} {name}: base {a1 + 1}-{a2} -> later {b1 + 1}-{b1 + a2 - a1}' + ('' if eq else f'; base lines differing {diff}'))
cmp('header, imports, module docstring, definitions, laws, the three landed privates', 0, 375, 0)
cmp("the target's docstring before (d)", a_doc, a_d, b_doc)
cmp("the target's statement and the suffices", a_t, a_t + 8, b_t)
cmp("exists_diagonalizer with its docstring, to the end", a_x, len(A), b_x)
print('region (b) in the later file: lines 376 -', b_doc, f'({b_doc - 375} lines)')
print('region (d) base', a_d + 1, '-', a_t, '-> later', b_d + 1, '-', b_t)
print('region (c) base:', repr(A[a_t + 8]), '-> later:', repr(B[b_t + 8]))
