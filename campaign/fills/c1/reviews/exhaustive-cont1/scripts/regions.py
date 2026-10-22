"""Owned-region check for ClassNP/ExhaustiveReplay.lean: base vs head.
usage: python3 -I regions.py <base file> <head file>"""
import sys, difflib
b = open(sys.argv[1], encoding='utf-8').read().split('\n')
h = open(sys.argv[2], encoding='utf-8').read().split('\n')
sm = difflib.SequenceMatcher(a=b, b=h, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
for tag, i1, i2, j1, j2 in ops:
    print(f'{tag}: base lines {i1+1}..{i2} ({i2-i1}) -> head lines {j1+1}..{j2} ({j2-j1})')
    if i2 > i1: print('   base text removed:', [b[i] for i in range(i1, i2)])
ok = True
# (a) imports: inserted after base line 7, exactly the three authorized lines
A = ['import TCSlib.Complexity.TuringMachine.ChoiceReplay',
     'import TCSlib.Complexity.TuringMachine.Build.StepClock',
     'import TCSlib.Complexity.TuringMachine.Build.Seam']
oa = [o for o in ops if o[1] == 7 and o[2] == 7]
ok &= len(oa) == 1 and h[oa[0][3]:oa[0][4]] == A
print('(a) three authorized imports inserted after base line 7, nothing else:', bool(oa) and h[oa[0][3]:oa[0][4]] == A)
# (b) home: insertion after base line 42 (blank, after namespace Turing)
ob = [o for o in ops if o[1] == 42 and o[2] == 42 and o[0] == 'insert']
print('(b) base line 41 =', repr(b[40]), '; base line 42 =', repr(b[41]), '; insertion after base line 42:', bool(ob),
      '(%d lines)' % (ob[0][4] - ob[0][3]) if ob else '')
ok &= bool(ob) and b[40] == 'namespace Turing' and b[41] == ''
# (c) body: base line 65 `  sorry` replaced
oc = [o for o in ops if o[1] == 64 and o[2] == 65]
print('(c) base line 65 =', repr(b[64]), '; replaced:', bool(oc), '(%d lines)' % (oc[0][4] - oc[0][3]) if oc else '')
ok &= bool(oc) and b[64] == '  sorry'
print('hunks:', len(ops), '; all in regions (a)-(c), (d) unused:', ok and len(ops) == 3)
# reversal: remove the inserted blocks, restore the sorry -> base
hh = list(h)
for tag, i1, i2, j1, j2 in sorted(ops, key=lambda o: -o[3]):
    hh[j1:j2] = b[i1:i2]
print('reversal equals base byte for byte:', '\n'.join(hh) == '\n'.join(b))
