<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: fourierCoeff_lowDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fourier coefficients of the low-degree truncation

**Claim.** `fourierCoeff (lowDegreePart f k) S = if S.card ≤ k then fourierCoeff f S else 0`.
Truncating the expansion truncates the coefficients, and changes nothing else.

**Proof.** Everything is done at the unfolded level: `lowDegreePart`,
`BooleanAnalysis.fourierCoeff`, `innerProduct` and `expect` are all unfolded and
`beta_reduce`d, then `w := uniformWeight n` and `fhat T := w * ∑ y, f y * chiS T y`
are abbreviated with `set`.

- `step1` — exchange the order of summation:
  `w * ∑ x, (∑ T, if |T| ≤ k then fhat T · χ_T(x) else 0) · χ_S(x)`
  becomes `∑ T, if |T| ≤ k then fhat T · (w * ∑ x, χ_T(x)·χ_S(x)) else 0`,
  via `Finset.mul_sum`, `Finset.sum_mul`, a `simp_rw` that pushes `χ_S(x)` inside
  the `if` (`split_ifs <;> ring`), and `Finset.sum_comm`.
- `ortho` — orthonormality of the characters: `fourier_coeff_chi T S` with
  `innerProduct`/`expect` unfolded says `w * ∑ x, χ_T(x)·χ_S(x) = if T = S then 1 else 0`.
- Collapse the nested guards (`if |T| ≤ k then (if T = S then fhat T else 0) else 0`
  rewritten as `if T = S then (if |S| ≤ k then fhat S else 0) else 0`, by
  `split_ifs <;> simp_all`) and `Finset.sum_ite_eq'` extracts the `T = S` term. ∎

**Remark.** The proof has to work with unfolded sums because the development has
no linearity lemma for `fourierCoeff` (no `fourierCoeff_add`/`fourierCoeff_sum`
in `BooleanAnalysis/Basic.lean`). The same twenty-line pattern is duplicated as
the `hcoeff` step inside `lowDegreePart_depends_on_influential`, with the guard
`|S| ≤ k` replaced by `|S| ≤ k ∧ ¬S ⊆ J`.

**Used in.** `lowDegree_l2_error` (the `hfour` step). No call sites outside
`BooleanAnalysis/KKL.lean`.
