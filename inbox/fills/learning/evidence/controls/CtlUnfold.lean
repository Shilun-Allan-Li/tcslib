import TCSlib.Cryptography.Randomness.Learning.Random

/-! Negative control: exactly one unfolding of a helper `def` (`LearnPRF.firstBit`, of
`Learning/Sample.lean`) by `rfl`. Passes unsealed; must fail exactly once under every seal. -/

theorem ctl_unfold_firstBit {n : ℕ} (y : Fin n → Bool) :
    TCSlib.Cryptography.Randomness.LearnPRF.firstBit y = (List.ofFn y).headD false := rfl
