<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: pmOne_apply_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A false bit maps to +1 under the ±1 embedding

**Claim.** Let `x : BitVec n` and `i : Fin n` with `x i = false`. Then
`pmOne x i = (1 : ℝ)`, where `pmOne x` is the Euclidean vector
`fun i => if x i then -1 else 1`.

**Proof.** Immediate from `simp [pmOne, h]`: unfolding `pmOne` exposes the
`if`, and the hypothesis `h : x i = false` selects the `1` branch.

**Remark.** The companion of `pmOne_apply_true`, also `@[simp]`. Together the
two lemmas let coordinate sums over `pmOne x` be split according to the bits of
`x`, which is how `coord_mul_pmOne` and `inner_pmOne_ones` proceed.
