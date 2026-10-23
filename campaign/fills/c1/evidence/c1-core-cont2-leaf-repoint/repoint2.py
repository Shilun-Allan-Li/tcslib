"""repoint2.py <NDCodeSimulator.lean>: the seam chain's numeral entry/exit states of the rewind phases."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(a, b, n=1):
    global s
    c = s.count(a); assert c == n, (a[:60], c); s = s.replace(a, b)
rep("  let S₂ := seamCompTM A₁ (Sum.inr ()) A₂ 0\n", "  let S₂ := seamCompTM A₁ (Sum.inr ()) A₂ InputRewindPhase.start\n")
rep("  let S₃ := seamCompTM S₂ (Sum.inr 2) A₃\n", "  let S₃ := seamCompTM S₂ (Sum.inr InputRewindPhase.done) A₃\n")
rep("  let S₇ := seamCompTM S₆ (Sum.inr doneW) A₂ 0\n", "  let S₇ := seamCompTM S₆ (Sum.inr doneW) A₂ InputRewindPhase.start\n")
rep("  let S₈ := seamCompTM S₇ (Sum.inr 2) A₈ RewindPhase.start\n", "  let S₈ := seamCompTM S₇ (Sum.inr InputRewindPhase.done) A₈ RewindPhase.start\n")
open(p, 'w', encoding='utf-8').write(s); print('ok')
