import TCSlib.Cryptography.SecureComputation.ObliviousTransfer

/-! Negative control: exactly one unfolding of a foreign `def` (`Complexity.NUPPT.layout`, of
`Randomized/Closure.lean`, read by the helpers only through `layout_eq` and the `in*_layout`
readers) by `rfl`. Passes unsealed; must fail exactly once under every seal. -/

theorem ctl_unfold_layout (u y α r : List Bool) :
    Complexity.NUPPT.layout u y α r = Turing.pairEncode (Turing.pairEncode (Turing.pairEncode u y) α) r :=
  rfl
