<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_proj_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Projecting off a unit vector preserves non-positive inner products

**Claim.** In a real inner product space `V`, let `u x y : V` with `‖u‖ = 1`,
`⟪x, u⟫ ≤ 0`, `⟪y, u⟫ ≤ 0` and `⟪x, y⟫ ≤ 0`. Then

`⟪x - ⟪x, u⟫ • u, y - ⟪y, u⟫ • u⟫ ≤ 0`,

i.e. the components of `x` and `y` orthogonal to `u` again have non-positive
inner product.

**Proof.**

1. `simp_all [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]`
   expands the inner product of the two differences into
   `⟪x, y⟫ - ⟪y,u⟫*⟪x,u⟫ - ⟪x,u⟫*⟪u,y⟫ + ⟪x,u⟫*⟪y,u⟫*⟪u,u⟫`.
2. `simp_all [real_inner_comm, inner_self_eq_norm_sq_to_K]` identifies
   `⟪u, y⟫ = ⟪y, u⟫` and, using `‖u‖ = 1`, replaces `⟪u, u⟫` by `1`, so the
   expression collapses to `⟪x, y⟫ - ⟪x, u⟫ * ⟪y, u⟫`.
3. `nlinarith` finishes: `⟪x, u⟫ * ⟪y, u⟫ ≥ 0` since both factors are
   non-positive, and `⟪x, y⟫ ≤ 0`.

**Remark.** A standalone helper stated for an abstract inner product space;
the version actually invoked by `rankin_bound_general` is
`orthProj_inner_nonpos`, which proves the same statement phrased through the
named `orthProj` and with the arguments in the `⟪u, ·⟫` order.
