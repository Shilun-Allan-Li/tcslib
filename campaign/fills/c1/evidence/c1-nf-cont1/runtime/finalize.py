#!/usr/bin/env python3
"""finalize.py <file>: region (c), the target's body, and region (d), the status phrases."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
old_body = """        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  sorry
"""
new_body = """        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  obtain ⟨M, hM⟩ := nf_pack (nf_host N)
  refine ⟨M, nf_C N.k, fun x t hN => (hM x _).2 (nf_forward N x t hN), fun x t hMt => ?_⟩
  obtain ⟨w, -, hh, ho⟩ := (hM x t).1 hMt
  exact nf_backward_host N x w hh ho
"""
assert s.count(old_body) == 1
s = s.replace(old_body, new_body)
old1 = """* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded normal form
  (statement; proof incomplete)."""
new1 = """* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded normal form."""
assert s.count(old1) == 1; s = s.replace(old1, new1)
old2 = """cited through [AB09, §3.2]; statement; proof incomplete): every"""
new2 = """cited through [AB09, §3.2]): every"""
assert s.count(old2) == 1; s = s.replace(old2, new2)
open(p, 'w', encoding='utf-8').write(s)
print("finalized")
