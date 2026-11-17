import TCSlib.Complexity.CircuitComplexity.NANDLayering
example {l : List ℕ} {k y₀ : ℕ} (h : ∀ y ∈ l, y = k) (h₀ : y₀ ∈ l) : l.foldr max 0 = k := by
  exact?
example {l : List ℕ} {k : ℕ} (h : ∀ y ∈ l, y ≤ k) : l.foldr max 0 ≤ k := by
  exact?
