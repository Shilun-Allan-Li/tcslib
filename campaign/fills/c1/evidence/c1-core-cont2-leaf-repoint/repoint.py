"""repoint.py <NDCodeSimulator.lean>: #151's private input-rewind leaf re-pointed to Build/InputRewind."""
import sys, re
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(old, new, n=1):
    global s
    c = s.count(old); assert c == n, (old[:70], c, n); s = s.replace(old, new)
start = "/-- The interpreter's native-input rewind leaf: one unconditional left move, a left scan to\n"
stop_after = "      rw [MultiTapeTM.runFrom_succ_eq_step, hstay u (by omega)]\n      simp\n\n"
assert s.count(start) == 1 and s.count(stop_after) == 1
i = s.index(start); j = s.index(stop_after) + len(stop_after); assert i < j
cut = s[i:j]
assert cut.count('private def ic_rewindLeafTM') == 1 and cut.count('private theorem ic_rewind_scan') == 1
assert cut.count('private theorem ic_rewind_leaf_run') == 1 and cut.count('private ') == 3
s = s[:i] + s[j:]
assert 'Fin 3' not in s[:i]
# the uses
rep("ic_rewindLeafTM K", "inputRewindTM K", 6)
rep("obtain ⟨hL1, hL2⟩ := ic_rewind_leaf_run ", "obtain ⟨hL1, hL2, -⟩ := inputRewindTM_run ")
rep("obtain ⟨hL1', hL2'⟩ := ic_rewind_leaf_run", "obtain ⟨hL1', hL2', -⟩ := inputRewindTM_run")
rep("(0 : Fin 3)", "InputRewindPhase.start", s.count("(0 : Fin 3)"))
rep("(2 : Fin 3)", "InputRewindPhase.done", s.count("(2 : Fin 3)"))
rep("Fin 3", "InputRewindPhase", s.count("Fin 3"))
rep("(inputRewindTM K) 0)", "(inputRewindTM K) InputRewindPhase.start)", 3)
rep("import TCSlib.Complexity.TuringMachine.Build.Rewind\n", "import TCSlib.Complexity.TuringMachine.Build.Rewind\nimport TCSlib.Complexity.TuringMachine.Build.InputRewind\n")
for gone in ("ic_rewindLeafTM", "ic_rewind_leaf_run", "ic_rewind_scan", "Fin 3"):
    assert gone not in s, gone
open(p, 'w', encoding='utf-8').write(s)
print("ok")
