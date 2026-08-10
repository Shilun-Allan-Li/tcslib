<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: contractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise operator is an L² contraction when ρ² ≤ 1

**Claim.** For every `ρ : ℝ` with `ρ ^ 2 ≤ 1` and every `f : BooleanFunc n`,
`expect (fun x => noiseOp ρ f x ^ 2) ≤ expect (fun x => f x ^ 2)`. This is the
`q = 2` case of hypercontractivity: no bound on `ρ` beyond `|ρ| ≤ 1` is needed.

**Proof.** Both sides are inner products, so the statement is Parseval plus a
termwise comparison of Fourier weights.

1. `expect (fun x => noiseOp ρ f x ^ 2) = innerProduct (noiseOp ρ f) (noiseOp ρ f)`
   and `expect (fun x => f x ^ 2) = innerProduct f f`, each by
   `simp [innerProduct, sq]`.
2. Rewrite the left side by `noise_l2_fourier` into
   `∑ S, (ρ ^ S.card) ^ 2 * fourierCoeff f S ^ 2`, and the right side by
   `parseval` into `∑ S, fourierCoeff f S ^ 2`.
3. Compare summand by summand (`Finset.sum_le_sum`). Fix `S` and rewrite
   `(ρ ^ S.card) ^ 2 = (ρ ^ 2) ^ S.card` (`ring`).
4. Since `0 ≤ ρ ^ 2` and `ρ ^ 2 ≤ 1`, `pow_le_one₀` gives `(ρ ^ 2) ^ S.card ≤ 1`,
   and `mul_le_of_le_one_left` (with `sq_nonneg`) drops the factor. ∎

**Used in.** `hypercontractivity_2_2`, which is exactly this statement with the
right-hand side written as `(expect (fun x => f x ^ 2)) ^ 1`.
