import TCSlib.Cryptography.Asymptotic.Universal

/-! Negative control for `PolyExpr.eval`: exactly one unfolding of `Complexity.PolyExpr.eval` by
`rfl`. Passes unsealed and under the A seals (`PolyExpr.eval` excluded as notation); must fail
exactly once under the B seals. -/

theorem ctl_unfold_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 := rfl
