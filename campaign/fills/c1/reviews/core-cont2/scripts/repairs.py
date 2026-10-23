"""The review's seal repairs (proof-only, six sites in three declarations). Every edit asserts that its
old text occurs exactly once. usage: python3 -I repairs.py <file>"""
import sys
p = sys.argv[1]; t = open(p, encoding='utf-8').read()
E = [
 # ic_rewind_scan, zero case: read runFrom through runFrom_succ_eq_step / runFrom_zero (was `show … step …`)
 ("    refine ⟨?_, ?_⟩\n    · show (ic_rewindLeafTM k).step cfg = _\n      rw [hstep, hm]\n    · intro u hu\n      obtain rfl : u = 0 := by omega\n      exact hs\n",
  "    refine ⟨?_, ?_⟩\n    · rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, hstep, hm]\n    · intro u hu\n      obtain rfl : u = 0 := by omega\n      rw [MultiTapeTM.runFrom_zero]\n      exact hs\n"),
 # ic_rewind_scan, successor case, u = 0 (was `exact hs` against `runFrom cfg 0`)
 ("      cases u with\n      | zero => exact hs\n      | succ u =>\n        rw [MultiTapeTM.runFrom_succ_eq_step]\n        exact hstay u (by omega)\n",
  "      cases u with\n      | zero =>\n        rw [MultiTapeTM.runFrom_zero]\n        exact hs\n      | succ u =>\n        rw [MultiTapeTM.runFrom_succ_eq_step]\n        exact hstay u (by omega)\n"),
 # ic_rewind_leaf_run: the first step through runFrom_succ_eq_step (was runFrom_add + `show … step …`)
 ("  have htime : cfg.inputPos.val + 1 = 1 + (cfg.inputPos.val - 1 + 1) := by omega\n  refine ⟨?_, ?_⟩\n  · rw [htime, MultiTapeTM.runFrom_add]\n    show (ic_rewindLeafTM k).runFrom ((ic_rewindLeafTM k).step cfg) _ = _\n    rw [hrun, hstep]\n",
  "  have htime : cfg.inputPos.val + 1 = cfg.inputPos.val - 1 + 1 + 1 := by omega\n  refine ⟨?_, ?_⟩\n  · rw [htime, MultiTapeTM.runFrom_succ_eq_step, hrun, hstep]\n"),
 # the target's verdict: no instance identification through `CodeNDTM.toFinNDTM` (was `rw [if_pos hP, …]`)
 ("    · rw [if_pos hP, decide_eq_true hP]\n    · rw [if_neg hP, decide_eq_false hP]\n",
  "    · simp only [hP, and_self, decide_true, if_true]\n    · simp only [hP, decide_false, if_false]\n"),
]
for i, (a, b) in enumerate(E, 1):
    n = t.count(a)
    assert n == 1, f'edit {i}: old text occurs {n} times'
    t = t.replace(a, b)
open(p, 'w', encoding='utf-8').write(t)
print(f'applied {len(E)} edits')
