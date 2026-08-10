<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: holder_sharpness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Hölder's inequality is attained on the cube

**Claim.** Let `p, q` be Hölder conjugates (`Real.HolderConjugate p q`) and
`u : BooleanFunc n`. Then there is `f : BooleanFunc n` with

```
(expect (fun x => |f x| ^ p)) ^ (1/p) ≤ 1   and
(expect (fun x => |u x| ^ q)) ^ (1/q) ≤ innerProduct f u
```

so the `L^q` norm of `u` is realised as a pairing against a function of `L^p`
norm at most one.

**Proof.** `refine'` supplies the explicit dual witness

```
f x = Real.sign (u x) * |u x| ^ (q - 1) / N,   N = (expect fun x => |u x| ^ q) ^ (1/p)
```

then proves the two conjuncts, each after a `by_cases` on the degenerate case
`N = 0` / `𝔼[|u|^q] = 0` (closed by `expect_const_eq` and by
`unfold innerProduct expect; norm_num` respectively).

1. **Norm bound.** Pointwise, `(|sign (u x)| · |u x| ^ (q-1) / N) ^ p =
   |u x| ^ q / N ^ p` by `Real.div_rpow`, `Real.mul_rpow`, `|sign| = 1` off the
   zero set, and the conjugacy identity `p * (q - 1) = q`
   (`hpq.symm.sub_one_mul_conj`). Summing (`Finset.sum_div`) gives
   `𝔼[|f|^p] = 𝔼[|u|^q] / N^p`, and `N ^ p = 𝔼[|u|^q]` (`← Real.rpow_mul`,
   `mul_inv_cancel₀ (ne_of_gt hpq.pos)`), so `div_self` makes it exactly `1`.
2. **Pairing bound.** Pointwise `|u x| ^ (q-1) * sign (u x) * u x = |u x| ^ q`
   (`Real.sign` opened by `split_ifs`, then `Real.rpow_add_one` per branch), so
   `innerProduct f u = 𝔼[|u|^q] / N`, rewritten as `(𝔼[|u|^q]) ^ (1 - p⁻¹)` by
   `Real.rpow_sub` (positivity via `expect_nonneg_of_nonneg`). As
   `1 - p⁻¹ = q⁻¹` (`hpq.symm.inv_add_inv_eq_one`) this is the `L^q` norm — the
   inequality in fact holds with equality. ∎

**Used in.** `noise_operator_duality` here, and four times in
`Hypercontractivity/General.lean`, where it converts an `L^q` norm bound into a
pairing bound so Cauchy–Schwarz plus `(p,2)`-hypercontractivity applies.
