<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: finrank_orthogonal_span_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The orthogonal complement of a unit vector drops the dimension by one

**Claim.** Let `V` be a finite-dimensional real inner product space and
`u : V` with `‖u‖ = 1`. Then
`Module.finrank ℝ (Submodule.span ℝ {u})ᗮ = Module.finrank ℝ V - 1`
(ℕ-subtraction).

**Proof.**

1. `finrank_span_singleton` gives `finrank ℝ (ℝ ∙ u) = 1`; its hypothesis
   `u ≠ 0` follows because `simp [h] at hu` turns `u = 0` into `0 = 1` against
   `‖u‖ = 1`.
2. `Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)` gives
   `finrank (ℝ ∙ u) + finrank (ℝ ∙ u)ᗮ = finrank V`.
3. `omega` combines the two into the stated (truncated) subtraction.

**Used in.** `rankin_bound_general`, step 3: it identifies the complement's
dimension as `d` when `finrank ℝ V = d + 1`, which is the measure the
induction recurses on.
