<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: pmOne_apply_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A true bit maps to −1 under the ±1 embedding

**Claim.** Let `x : BitVec n` and `i : Fin n` with `x i = true`. Then
`pmOne x i = (-1 : ℝ)`, where `pmOne x` is the Euclidean vector
`fun i => if x i then -1 else 1`.

**Proof.** Immediate from `simp [pmOne, h]`: unfolding `pmOne` exposes the
`if`, and the hypothesis `h : x i = true` selects the `-1` branch.

**Remark.** One half of the coordinate-evaluation pair for `pmOne` (with
`pmOne_apply_false`), marked `@[simp]`. It fixes the sign convention: `true`
bits become `-1`.
