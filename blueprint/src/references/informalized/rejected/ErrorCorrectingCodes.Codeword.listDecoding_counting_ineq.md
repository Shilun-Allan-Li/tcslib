<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: listDecoding_counting_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The counting inequality holds at rate 1 − H_q(ρ) − 1/L

**Claim.** Let `2 ≤ q`, `1 ≤ L`, `r = 1 - qaryEntropy q p - 1/L`,
`M = ⌊q^(r*n)⌋₊`, `V = ⌊q^(qaryEntropy q p * n)⌋₊` (real `rpow`), and assume
`0 < M`, `M ≤ q^n`, `L < M`. Then

```
q^n · C(V, L+1) · C(q^n - (L+1), M - (L+1))  <  C(q^n, M).
```

**Proof.** Divide by `C(q^n, M)` and bound the three factors.

1. `h_binom_ratio`: `C(q^n - (L+1), M - (L+1)) / C(q^n, M) ≤ (M/q^n)^(L+1)`,
   by `binom_ratio_bound (q^n) M (L+1)` (side conditions by `linarith`).
2. `h_binom_bound`: `C(V, L+1) ≤ V^(L+1) / (L+1)!` (`Nat.choose_le_pow_div`).
3. `h_combined`: `q^n · (V^(L+1)/(L+1)!) · (M/q^n)^(L+1) < 1`. Replace `V` and
   `M` by their unfloored values `q^(H_q(p)·n)` and `q^(r·n)`
   (`Nat.floor_le`, monotonicity via `gcongr`), leaving
   `q^n · (q^{H_q(p)n})^{L+1} · (q^{rn}/q^n)^{L+1} / (L+1)!`. Since
   `H_q(p) + r - 1 = -1/L`, the exponent collapses to
   `n·(1 - (L+1)/L) = -n/L` (`Real.rpow_add`, `Real.rpow_sub`,
   `Real.rpow_neg`, `← Real.rpow_mul`, then `ring_nf`/`field_simp`). The
   resulting `q^(-n/L) / (L+1)! < 1` is `h_simplified`: the numerator is `≤ 1`
   because the exponent is nonpositive
   (`Real.rpow_le_rpow_of_exponent_le` with `q ≥ 1`), and
   `(L+1)! ≥ L + 1 ≥ 2` (`Nat.self_le_factorial`).
4. Multiply back: `div_le_iff₀` on step 1, then
   `mul_le_mul_of_nonneg_left/right` with step 2, and
   `mul_lt_mul_of_pos_right h_combined (Nat.choose_pos hM_le)` gives the strict
   inequality after `ring`.

**Used in.** `list_decoding_capacity`, as the hypothesis `h_ineq` of
`exists_listDecodable_code`.
