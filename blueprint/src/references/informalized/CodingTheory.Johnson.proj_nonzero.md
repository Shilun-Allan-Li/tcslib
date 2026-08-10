<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: proj_nonzero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Projecting a unit vector off `u` kills it only if it was ±u

**Claim.** In a real inner product space `V`, let `u x : V` be unit vectors
(`‖u‖ = 1`, `‖x‖ = 1`) with `inner ℝ x u ≤ 0`, and suppose `x ≠ -u` and
`x ≠ u`. Then `x - (inner ℝ x u) • u ≠ 0`.

**Proof.** `contrapose! hne'`, so it suffices to derive `x = u` from
`x - (inner ℝ x u) • u = 0`.

1. `sub_eq_zero.mp` turns that equation into `∃ α : ℝ, x = α • u` (`obtain`).
2. `simp_all [norm_smul, inner_smul_left]` uses `‖x‖ = ‖u‖ = 1` to reduce the
   norm equation to `|α| = 1`.
3. `rw [abs_eq] at hx <;> aesop` splits `α = 1` from `α = -1`; the `α = -1`
   branch contradicts `x ≠ -u`, leaving `x = u`.

**Remark.** The `inner ℝ x u ≤ 0` hypothesis is not needed for the argument —
it is carried because every call site already has it. `orthProj_ne_zero` is the
same statement phrased for the named `orthProj` operator (with the inner product
written `inner ℝ u v`), and that is the version the Rankin bound uses.
