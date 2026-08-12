<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: lowDegree_l2_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# L2 error of low-degree truncation is the tail Fourier weight

**Claim.** `l2DistSq f (lowDegreePart f k) = ∑ S, if k < S.card then fourierCoeff f S ^ 2 else 0`.
The error of dropping the high levels is exactly the Fourier weight above `k`.

**Proof.**

- `hfg`: `f x - lowDegreePart f k x = highDegreePart f k x`, from
  `low_plus_high_eq f k x` by `linarith`.
- `step2`: rewriting the difference with `hfg` turns the definition of
  `l2DistSq` into `innerProduct (highDegreePart f k) (highDegreePart f k)`
  (unfold `l2DistSq`, `innerProduct`, `expect`; `sq` splits the square into a
  product).
- `parseval` converts that inner product into `∑ S, fourierCoeff (highDegreePart f k) S ^ 2`.
- `hfour`: the coefficient is `if k < S.card then f̂(S) else 0`. Proved by
  rewriting `highDegreePart f k` as `fun x => f x - lowDegreePart f k x`
  (`funext` on `hfg`), splitting the unfolded sum along the subtraction
  (`mul_sub`, `Finset.sum_sub_distrib`), and applying
  `fourierCoeff_lowDegreePart`; the two `by_cases` branches use
  `Nat.not_lt.mpr` / `Nat.lt_of_not_le`.
- Substituting `hfour` and squaring the guarded value (`split_ifs <;> simp`)
  gives the claim. ∎

**Used in.** `lowDegree_approx`, which combines it with
`tail_fourier_weight_bound` to get `l2DistSq f (lowDegreePart f k) ≤ I[f]/k` —
the low-degree half of `friedgut_junta`. No call sites outside
`BooleanAnalysis/KKL.lean`.
