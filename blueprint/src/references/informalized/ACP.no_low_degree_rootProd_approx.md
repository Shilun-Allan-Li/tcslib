<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: no_low_degree_rootProd_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The top monomial has no degree-`d` approximant, given the counting bound

**Claim.** Fix finite `K`, `ω ≠ 0`, and `n d e : ℕ`. Assume

- `hrepr`: every `f : rootCube ω n → K` is computed on the cube by some squarefree
  (multilinear) polynomial `squarefreePolynomial c`, and
- `hcounting`: it is *not* the case that every `f` admits `Q` with
  `Q.totalDegree ≤ n / 2 + d` and `rootCubeBadCount ω f Q ≤ e`.

Then there is no `P` with `P.totalDegree ≤ d` and
`rootCubeBadCount ω (fun x => ∏ i, x.1 i) P ≤ e`.

**Proof.** Contrapositive in three lines.

1. `intro htop` and `rcases` the existential into `P`, `hdeg`, `happrox`.
2. `apply hcounting`, then `intro f`.
3. `rootProd_approx_implies_all_functions_approx` applied to `hω0`, `hrepr`, `P`,
   `hdeg`, `happrox`, `f` produces exactly the required degree-`≤ n / 2 + d`
   approximant for `f`, contradicting `hcounting`.

**Remark.** All the mathematics is in the two inputs: `hrepr` (multilinear
representation on `{1, ω}^n`) and the previous lemma's splitting
`F = F₁ + (∏ i, x i) · F₂(1 + ω⁻¹ - ω⁻¹ x)`. `hcounting` is left as a hypothesis so
that the entropy/binomial estimate can be supplied separately — see
`rootCube_counting_obstruction` and `no_low_degree_rootProd_approx_of_finite_counting`.

**Used in.** `no_low_degree_rootProd_approx_of_finite_counting`, and
`no_low_degree_rootProd_approx_concrete` in `LowDegreeObstruction.lean`.
