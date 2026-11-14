import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games

/-! Negative control for `PolyExpr.eval`: exactly one unfolding of `Complexity.PolyExpr.eval` by
`rfl`. Passes unsealed and under seal A (`PolyExpr.eval` excluded); must fail exactly once under
seal B (`PolyExpr.eval` sealed). -/

theorem ctl_unfold_eval : (Complexity.PolyExpr.const 1).eval 5 = 1 := rfl
