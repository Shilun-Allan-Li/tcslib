<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegree_squarefree_complete_on_rootCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every degree-`≤ D` polynomial is squarefree-representable on the root cube

**Claim.** Let `K` be a field, `ω ≠ 1`, and `Q : MvPolynomial (Fin n) K` with
`Q.totalDegree ≤ D`. Then there are coefficients `c : LowDegreeSupport n D → K` with
`(lowDegreeSquarefreePolynomial c).eval x.1 = Q.eval x.1` for every `x : rootCube ω n`.
That is, the concrete low-degree squarefree family is complete for degree-`≤ D` polynomial
functions on `{1,ω}^n`.

**Proof.**
- For each monomial `m ∈ Q.support`, let `rep m` be the coefficient family produced by
  `monomial_lowDegree_squarefree_complete_on_rootCube` for `monomial m (Q.coeff m)`, obtained
  by `Classical.choose`; the degree side condition is `MvPolynomial.le_totalDegree` composed
  with `hQdeg` via `le_trans`. Outside the support, `rep m := 0`.
- Take `c s := ∑ m ∈ Q.support, rep m s`.
- `hrep`: for `m ∈ Q.support`, `(lowDegreeSquarefreePolynomial (rep m)).eval x.1` equals
  `((monomial m) (Q.coeff m)).eval x.1` — this is `Classical.choose_spec` of the same
  application, discharged with `simpa [rep, hm, hcoeff_ne]` (`MvPolynomial.mem_support_iff`
  gives `Q.coeff m ≠ 0`, which selects the right branch of `rep`).
- The final `calc`: `lowDegreeSquarefreePolynomial_sum` moves the sum over `Q.support` out of
  the constructor; `simp` pushes `eval` through the finite sum; `Finset.sum_congr` with `hrep`
  replaces each summand by the monomial's value; and `map_sum` together with
  `MvPolynomial.support_sum_monomial_coeff` reassembles `Q.eval x.1`.

**Used in.** `rootCube_counting_obstruction_lowDegreeSquarefree`, as the completeness
hypothesis of the abstract counting obstruction.
