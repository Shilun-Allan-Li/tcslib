<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: proj_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Squared norm of the component orthogonal to a unit vector

**Claim.** In any real inner product space `V`, for a unit vector `u` (`‖u‖ = 1`)
and any `x : V`,
`‖x - ⟪x, u⟫ • u‖^2 = ‖x‖^2 - ⟪x, u⟫^2`.
That is, removing the `u`-component of `x` subtracts exactly the square of that
component from the squared norm.

**Proof.**

1. `rw [@norm_sub_sq ℝ]` turns the left side into
   `‖x‖^2 - 2 * ⟪x, ⟪x,u⟫ • u⟫ + ‖⟪x,u⟫ • u‖^2`.
2. `simp [inner_smul_right]` evaluates the cross term as
   `⟪x, ⟪x,u⟫ • u⟫ = ⟪x,u⟫ * ⟪x,u⟫`.
3. `simp [hu, norm_smul]` evaluates the last term: `‖⟪x,u⟫ • u‖ = |⟪x,u⟫| * 1`,
   whose square is `⟪x,u⟫^2`.
4. `ring` (`ring_nf`) closes the resulting identity
   `‖x‖^2 - 2⟪x,u⟫^2 + ⟪x,u⟫^2 = ‖x‖^2 - ⟪x,u⟫^2`.

**Remark.** This is the Pythagoras identity for the orthogonal splitting
`x = (x - ⟪x,u⟫•u) + ⟪x,u⟫•u`, stated as a granular helper. It currently has no
consumer in the file: the Rankin-bound argument was rebuilt around the bundled
`orthProj` family (`orthProj_mem_orthogonal`, `orthProj_ne_zero`,
`orthProj_inner_nonpos`), which superseded this earlier `x - ⟪x,u⟫•u` group of
lemmas.
