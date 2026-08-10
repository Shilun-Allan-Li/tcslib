<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: binary_johnson_card_bound_parametric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Johnson bound for an arbitrary admissible shift

**Claim.** Let `C : Finset (BitVec n)` have pairwise Hamming distance at least
`d` and all weights at most `w`. Let `α : ℝ` with `0 ≤ α` be such that
(i) `shifted α x ≠ 0` for every `x ∈ C`, and (ii) the arithmetic inequality
`(n - 2*d) + α^2 * n + 2*α*(2*w - n) ≤ 0` holds. Then `C.card ≤ 2 * n`. This is
the parametric core: `α` is an input, so no formula for it appears here.

**Proof.** Write `u x = shifted α x = pmOne x - α • ones`.

1. Pairwise nonpositivity: for distinct `x y ∈ C`, `inner_shifted_le_expr`
   bounds `⟪u x, u y⟫` by the left-hand side of hypothesis (ii), so `linarith`
   with (ii) gives `⟪u x, u y⟫ ≤ 0`.
2. Let `U = C.image (fun x => normalize (u x))`. The normalization map is
   injective on `C`: if `normalize (u x) = normalize (u y)` then
   `u x = ‖u x‖ * ‖u y‖⁻¹ • u y`, and expanding `⟪u y, u x⟫` (`RCLike.wInner`,
   `Finset.mul_sum`) makes it a positive multiple of `∑ i, (u y i)^2 > 0`,
   contradicting step 1. Hence `U.card = C.card`
   (`Finset.card_image_of_injOn`).
3. `U` consists of unit vectors: `simp [normalize, norm_smul]` using
   `u x ≠ 0` from (i).
4. `U` has pairwise nonpositive inner products: `⟪normalize (u x),
   normalize (u y)⟫ = (‖u x‖ * ‖u y‖)⁻¹ * ⟪u x, u y⟫`, a nonnegative scalar
   times a nonpositive number (`mul_nonpos_of_nonneg_of_nonpos`); distinctness
   of the images forces `x ≠ y` so step 1 applies.
5. `rankin_finset_bound` gives `U.card ≤ 2 * n`, and `simpa [hcardU]`
   transports it to `C`. ∎

**Used in.** `binary_johnson_card_bound`, which instantiates `α := alpha n d`
and discharges (i) via `shifted_ne_zero_of_alpha_lt_one` and (ii) via
`johnson_arith`.
