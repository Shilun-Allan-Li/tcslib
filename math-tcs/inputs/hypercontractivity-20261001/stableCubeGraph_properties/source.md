User request: Begin filling Hypercontractivity sorries using Lean LSP, following existing sketches and policy.md. Keep theorem statements unchanged and proofs concise.

/-- The stable cube has nonnegative symmetric weights, uniform outgoing mass, and unit
total mass for `-1 ≤ ρ ≤ 1`. [OD14, Rem. 9.11]

**Proof sketch.** Each coordinate kernel is nonnegative and symmetric with row sum one.
Factor the finite sums and multiply by the uniform mass. -/
theorem stableCubeGraph_properties (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    (∀ x y, 0 ≤ (stableCubeGraph n ρ).edgeWeight x y) ∧
    (∀ x y, (stableCubeGraph n ρ).edgeWeight x y =
      (stableCubeGraph n ρ).edgeWeight y x) ∧
    (∀ x, ∑ y : BoolCube n, (stableCubeGraph n ρ).edgeWeight x y = uniformWeight n) ∧
    (∑ x : BoolCube n, ∑ y : BoolCube n, (stableCubeGraph n ρ).edgeWeight x y) = 1 := sorry