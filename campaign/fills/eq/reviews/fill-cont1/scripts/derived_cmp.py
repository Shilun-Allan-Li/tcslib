"""Is a worker-derived file (sealed copy, axiom copy) the head plus insertions only? (python3 -I)
Reports the inserted blocks (head line before which they sit) and whether every head line is kept
in order with no other change.
usage: python3 -I derived_cmp.py <head> <derived>"""
import difflib, sys
A = open(sys.argv[1], encoding='utf-8').read().split('\n'); B = open(sys.argv[2], encoding='utf-8').read().split('\n')
sm = difflib.SequenceMatcher(a=A, b=B, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
print(sys.argv[2].split('/')[-1], ': non-equal opcodes', len(ops))
for tag, a1, a2, b1, b2 in ops:
    print(f'  {tag}: head {a1 + 1}-{a2} ({a2 - a1} lines) -> derived {b1 + 1}-{b2} ({b2 - b1} lines); first inserted: {B[b1][:90]!r}')
print('only insertions:', all(o[0] == 'insert' for o in ops))
