<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: lp_norm_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Lᵖ norms on the cube increase in p

**Claim.** For `1 ≤ r ≤ s` and `f : BooleanFunc n`,

```
(expect (fun x => |f x| ^ r)) ^ (1/r) ≤ (expect (fun x => |f x| ^ s)) ^ (1/s)
```

the power-mean inequality for the uniform probability measure on `{0,1}ⁿ` (all
exponents are real `rpow`).

**Proof.**

1. `h_weight_sum`: the weights sum to one, `∑ x : BoolCube n, uniformWeight n = 1`,
   by `simp +decide [uniformWeight, Finset.card_univ]` (there are `2ⁿ` points of
   mass `2⁻ⁿ`).
2. `h_ineq`: `∑ x, w · |f x| ^ r ≤ (∑ x, w · |f x| ^ s) ^ (r/s)`. This is Jensen
   for the concave power `t ↦ t ^ (r/s)` on `Set.Ici 0`: concavity from
   `Real.concaveOn_rpow` (the exponent lies in `[0,1]` since `1 ≤ r ≤ s`), then
   `ConcaveOn.le_map_sum` with the weight and non-negativity side goals
   (`positivity`, `Real.rpow_nonneg`). Rewriting
   `(|f x| ^ s) ^ (r/s) = |f x| ^ r` via `← Real.rpow_mul` and
   `mul_div_cancel₀` matches it to the stated form.
3. Raise `h_ineq` to the power `1/r` with `Real.rpow_le_rpow`; unfolding `expect`
   and pushing the constant weight through the sum (`Finset.mul_sum`,
   `← Real.rpow_mul`, `ring_nf`, `norm_num` with `r ≠ 0`, `s ≠ 0`) identifies the
   two sides with the claimed norms. The final non-negativity obligation is
   `Finset.sum_nonneg` over non-negative weighted terms. ∎

**Note.** Stated for general `n`, but currently **unreferenced** elsewhere in the
library — an independent Lᵖ-monotonicity fact kept alongside the one-bit
development.
