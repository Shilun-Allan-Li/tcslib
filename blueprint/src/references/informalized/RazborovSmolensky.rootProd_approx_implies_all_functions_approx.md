<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootProd_approx_implies_all_functions_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A good approximant to the top monomial approximates everything

**Claim.** Let `ω ≠ 0` in a finite field `K`, and suppose `hrepr`: every
`f : rootCube ω n → K` is represented on the cube by `squarefreePolynomial c` for some
coefficient function `c`. If `P` has `P.totalDegree ≤ d` and approximates the top monomial
with at most `e` bad points, i.e. `rootCubeBadCount (fun x => ∏ i, x.1 i) P ≤ e`, then
*every* `f : rootCube ω n → K` admits a `Q` with `Q.totalDegree ≤ n / 2 + d` and
`rootCubeBadCount f Q ≤ e`.

**Proof.** Fix `f`, get `c` from `hrepr` and the pair `P₁, R` (each of degree `≤ n / 2`)
from `split_multilinear_at_half_degree_direct`. Set `Q = P₁ + P * R`.

* Degree: `MvPolynomial.totalDegree_mul` and `Nat.add_le_add` give
  `(P * R).totalDegree ≤ d + n / 2`; `MvPolynomial.totalDegree_add` bounds `Q.totalDegree`
  by `max P₁.totalDegree (P * R).totalDegree`, and `max_le` with `Nat.le_add_right` / `omega`
  finishes at `n / 2 + d`.
* Error: `Finset.card_le_card` shows the bad set of `Q` for `f` is contained in the bad set
  of `P` for the top monomial. Indeed, at any `x` where `P.eval x.1 = ∏ i, x.1 i`
  (`htop_eq`), a `calc` gives `Q.eval x.1 = P₁.eval x.1 + (∏ i, x.1 i) * R.eval x.1`
  `= (squarefreePolynomial c).eval x.1 = f x`, using `hsplit x` and `hc x`. Then
  `le_trans` with `happrox`.

**Remark.** Contrapositively: any function that is hard to approximate at degree `n / 2 + d`
certifies that the top monomial has no degree-`d` approximant — the shape consumed by
`no_low_degree_rootProd_approx`.
