
/-- **The predictor's output**: on `y` with coins `c = (c₁, c₂)` (the guessed bit and the
distinguisher's coins), `pkPredictor D flip` outputs `c₁` if `D` accepts `(y, c₁)` with coins `c₂`
and `¬c₁` otherwise, negated when `flip`,
`pkPredictor D flip y c = xor (if D (y, c.1) c.2 then c.1 else !c.1) flip`
[PS10, Theorem 104.4, proof]. -/
theorem pkPredictor_apply {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) (y : α)
    (c : Bool × ρ) : pkPredictor D flip y c = xor (if D (y, c.1) c.2 then c.1 else !c.1) flip :=
  rfl
