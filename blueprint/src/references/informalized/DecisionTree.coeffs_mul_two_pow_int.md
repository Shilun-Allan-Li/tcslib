<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: coeffs_mul_two_pow_int -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Granularity, multiplicative form

**Claim.** For `T : DecisionTree n`, `k : ℕ` with `T.depth ≤ k`, and any
frequency `S`, there is an integer `m` with `T.coeffs S * 2 ^ k = (m : ℝ)`.

**Proof.** `induction T generalizing k S` — both the exponent and the frequency
must be generalized, since the branch case recurses at `k - 1` and at `S ∆ {i}`.

1. **Leaf `b`.** Take the witness `if S = ∅ then (if b then -(2 ^ k) else 2 ^ k)
   else 0`, then `simp only [coeffs, boolToSign]` and
   `split_ifs <;> push_cast <;> ring`.
2. **Branch `i lo hi`.** Since `(.branch i lo hi).depth = 1 + max lo.depth
   hi.depth`, a `have hk1 : 1 ≤ k` follows from `le_trans` with
   `simp [DecisionTree.depth]`, so `obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1` is
   available.
3. `simp only [DecisionTree.depth] at hk` gives `max lo.depth hi.depth ≤ k'`,
   licensing four inductive-hypothesis instances at exponent `k'`: `m₁, m₂` for
   `lo, hi` at `S` and `m₃, m₄` for `lo, hi` at `S ∆ {i}` (the side goals by
   `omega`).
4. The witness is `m₁ + m₂ + m₃ - m₄`. After `simp only [coeffs]`, `push_cast`
   and `rw [pow_succ]`, the extra factor of `2` in `2 ^ (k' + 1)` cancels the
   two divisions by `2` in the branch clause, and
   `linear_combination h₁ + h₂ + h₃ - h₄` closes the goal.

**Remark.** The exponent is left free rather than fixed at `T.depth` precisely so
that the induction can descend to `k'`; the `T.depth` case is recovered in
`coeffs_granular`.

**Used in.** `coeffs_granular` (with `k := T.depth` and `le_rfl`).
