<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: binom_ratio_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binomial ratio bound

**Claim.** For naturals `k ≤ M ≤ N`, the real quotient of binomial
coefficients satisfies

```
C(N - k, M - k) / C(N, M) ≤ (M / N) ^ k.
```

**Proof.** The quotient is computed exactly as a product of `k` decreasing
ratios, then each factor is bounded.

1. `h_prod`: `C(N-k, M-k) / C(N, M) = ∏_{i ∈ range k} (M - i) / (N - i)`.
   Clear the denominator with `div_eq_iff` (nonzero by `Nat.choose_pos hM`),
   then use the subset-choice identity
   `C(N-k, M-k) * C(N, k) = C(N, M) * C(M, k)` (`Nat.choose_mul`, cast by
   `rw_mod_cast`), together with the falling-factorial expansions
   `C(M,k) = ∏_{i<k}(M-i) / k!` and `C(N,k) = ∏_{i<k}(N-i) / k!`
   (`Nat.descFactorial_eq_factorial_mul_choose`,
   `Nat.descFactorial_eq_prod_range`, casts by `Int.subNatNat_of_le`). A
   `by_cases` on `∏_{i<k}(N-i) = 0` discharges the degenerate branch
   (contradicts `Nat.choose_pos`), and `field_simp` finishes the other.
2. `h_le`: for `i < k`, `(M - i)/(N - i) ≤ M / N`. After `div_le_div_iff₀` this
   is `(M-i)·N ≤ M·(N-i)`, i.e. `i·M ≤ i·N`, given by `nlinarith` from
   `i + 1 ≤ M` and `M ≤ N`.
3. `Finset.prod_le_prod` (factors nonnegative by `div_nonneg` and
   `Nat.cast_le`) bounds the product by `(M/N)^k` via `Finset.prod_const` and
   `Finset.card_range`.

**Used in.** `listDecoding_counting_ineq`, with `N = q^n` and `k = L + 1`: it
converts the count of `M`-subsets containing a fixed `(L+1)`-set into the
probability-style factor `(M/q^n)^{L+1}`.
