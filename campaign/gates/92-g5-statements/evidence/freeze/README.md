# Freeze (gate 92)

`declfreeze.py <base> <head> [authorized]` on the three edited files, base = the campaign at
`057da7a7` (the merge base), head = `2339d2df`. `Encoding`'s run passes the three bodies the
factoring changes as authorized: `exists_codeTM_spaceUsed`, `FinTM.toCodeTM` and
`toCodeTM_computesInTime_iff`. The tool reads a pattern-matching definition's arms as part of its
statement, so it reports `FinTM.toCodeTM` as "statement changed". Its type,
`(M : FinTM Bool) → M.k = 1 → CodeTM`, is byte-identical (the `grep` lines below); only the arm's
right-hand side changes, now through `FinTM.stateEquivFin`.
Encoding-head.lean.txt:752:noncomputable def FinTM.toCodeTM : (M : FinTM Bool) → M.k = 1 → CodeTM
Encoding-base.lean.txt:741:noncomputable def FinTM.toCodeTM : (M : FinTM Bool) → M.k = 1 → CodeTM
