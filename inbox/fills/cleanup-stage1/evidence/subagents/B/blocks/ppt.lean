
/-- **The length of a coin string**: the list of the coins `r : A.Coins n` has length
`coins.eval n`, `(List.ofFn r).length = A.coins.eval n`.
Framework glue, no textbook counterpart. -/
protected theorem length_ofFn_coins (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, coinLen_eq]
