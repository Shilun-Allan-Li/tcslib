<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: monomial_lowDegree_squarefree_complete_on_rootCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Degree-preserving multilinearization of one monomial on `{1,ω}^n`

**Claim.** Let `K` be a field, `ω ≠ 1`, `m : Fin n →₀ ℕ` a monomial exponent vector with
total degree `m.sum (fun _ e => e) ≤ D`, and `a : K`. Then there are coefficients
`c : LowDegreeSupport n D → K` such that `lowDegreeSquarefreePolynomial c` and
`MvPolynomial.monomial m a` agree at every point of `rootCube ω n`. So one monomial of
degree `≤ D` is matched on the cube by a squarefree polynomial using only supports of size
`≤ D`.

**Proof.**
- Put `S := m.support`. `hS_card : S.card ≤ D`, since `Finset.card_eq_sum_ones` plus
  `Finset.sum_le_sum` gives `S.card ≤ ∑ i ∈ S, m i` (each exponent on the support is `≥ 1`,
  by `Nat.pos_of_ne_zero`), and `Finsupp.sum` identifies that sum with `m.sum`, which is
  `≤ D` by hypothesis.
- Affine interpolant per coordinate: with `hωm1 : ω - 1 ≠ 0` from `sub_ne_zero.mpr hω`, set
  `A i := (ω ^ m i - 1) * (ω - 1)⁻¹` and `B i := 1 - A i`. `hA_mul` records
  `A i * (ω - 1) = ω ^ m i - 1` via `inv_mul_cancel₀ hωm1`.
- `hcoord`: for every `i` and every cube point `x`, `A i * x.1 i + B i = x.1 i ^ m i`. Case
  split on `x.2 i` (value `1` or `ω`); the first case is `ring` after `simp [hx1]`, the second
  uses `hA_mul` and `ring`. This is the one-variable fact that a power is affine on `{1,ω}`.
- Candidate coefficients: `c t := a * (∏ i ∈ t, A i) * (∏ i ∈ S \ t, B i)` for `t ⊆ S`, and
  `0` otherwise.
- `heval_low`: evaluating `lowDegreeSquarefreePolynomial c` at `x` gives
  `∑ t ∈ S.powerset, c t * ∏ i ∈ t, x.1 i`. Proved by `MvPolynomial.eval_sum`, then
  `Finset.sum_subset` to drop all `t ⊄ S` (their coefficient is `0`), then `Finset.sum_congr`
  with `simp [squarefreeMonomial]` on the remaining terms, where `Finset.card_le_card` supplies
  the degree side condition `t.card ≤ D`.
- `hprod_expand`: that sum equals `a * ∏ i ∈ S, (A i * x.1 i + B i)`, by `Finset.mul_sum`,
  `Finset.prod_mul_distrib`, and `Finset.prod_add` — the subset-sum expansion of a product
  of binomials.
- `hprod_coord`: `Finset.prod_congr` with `hcoord` rewrites this as
  `a * ∏ i ∈ S, x.1 i ^ m i` = `a * m.prod (fun i e => x.1 i ^ e)`, i.e.
  `(monomial m a).eval x.1` by `MvPolynomial.eval_monomial`; a `calc` chains the four steps.

**Remark.** The point is degree preservation: replacing each power by its affine interpolant
never introduces a new variable, so the supports stay inside `S` and hence of size `≤ D`.
