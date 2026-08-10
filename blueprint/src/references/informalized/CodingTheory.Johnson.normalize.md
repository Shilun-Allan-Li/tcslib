<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: normalize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `normalize`: rescaling a Euclidean vector to unit length

**Definition.** For `u : Euc n`, `normalize u = (‖u‖)⁻¹ • u` — the vector `u`
divided by its own norm.

**Remark.** Nonzero-ness is not a hypothesis: since `‖0‖⁻¹ = 0` in Lean,
`normalize 0 = 0`, so `‖normalize u‖ = 1` holds only under `u ≠ 0`. Every use
site therefore carries that side condition explicitly. Because the scaling factor
is positive, `normalize` preserves the sign of inner products, which is the only
property the Johnson argument needs.

**Used in.** `binary_johnson_card_bound_parametric`, where the code `C` is mapped
to `U = C.image (fun x => normalize (shifted α x))` and the three facts about `U`
are established from the corresponding facts about `shifted α x`:

- `hunitU` : `‖normalize (u x)‖ = 1` via `norm_smul` and `hnonzero x`;
- `h_injOn` / `hcardU` : `U.card = C.card`, since two codewords with equal
  normalizations would have positive inner product, contradicting `hpair_u`
  (`Finset.card_image_of_injOn`);
- `hpairU` : `⟪normalize (u x), normalize (u y)⟫_[ℝ] = (1 / (‖u x‖ * ‖u y‖)) * ⟪u x, u y⟫_[ℝ]`,
  so non-positivity is inherited (`mul_nonpos_of_nonneg_of_nonpos`).

Together these hand `U` to `rankin_finset_bound`, giving `C.card ≤ 2 * n`.
