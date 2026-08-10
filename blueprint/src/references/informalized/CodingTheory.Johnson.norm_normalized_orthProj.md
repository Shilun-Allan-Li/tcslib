<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: norm_normalized_orthProj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The normalized orthogonal projection is a unit vector

**Claim.** In a real inner product space `V`, let `u v : V` with `‖u‖ = 1`,
`‖v‖ = 1`, `v ≠ u` and `v ≠ -u`. Then
`‖‖orthProj u v‖⁻¹ • orthProj u v‖ = 1`, where
`orthProj u v = v - ⟪u, v⟫ • u`.

**Proof.** A single `rw` chain: `norm_smul`, `norm_inv` and `norm_norm` reduce
the goal to `‖orthProj u v‖⁻¹ * ‖orthProj u v‖ = 1`, and
`inv_mul_cancel₀` discharges it, its non-vanishing side condition supplied by
`norm_ne_zero_iff.mpr (orthProj_ne_zero u v hu hv hne1 hne2)`.

**Used in.** `rankin_bound_general`, step 4: the image set `T'` under
`mkProj` consists of unit vectors of the orthogonal complement, which is what
lets the induction hypothesis apply in the smaller-dimensional space.
