import TCSlib.Cryptography.Asymptotic.Universal

/-! Negative control: exactly one unfolding of a foreign `def` (`Turing.codeDecode`, of
`CodeFormat.lean`) by `rfl`. Passes unsealed; must fail exactly once under every seal. -/

theorem ctl_unfold_codeDecode (xs : List Bool) :
    Turing.codeDecode xs = Turing.oneTapeFormat.decode xs := rfl
