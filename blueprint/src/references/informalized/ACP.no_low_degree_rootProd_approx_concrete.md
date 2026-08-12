<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: no_low_degree_rootProd_approx_concrete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# No low-degree polynomial approximates the coordinate product on `{1,ω}^n`

**Claim.** Let `K` be a finite field, `ω ≠ 0`, `ω ≠ 1`, and `n d e B : ℕ`. Assume
`∑ t ∈ range (e + 1), (2 ^ n).choose t * (Fintype.card K) ^ t ≤ B` and
`Fintype.card K ^ (2 ^ n) > Fintype.card (LowDegreeSupport n (n / 2 + d) → K) * B`. Then
there is no `P : MvPolynomial (Fin n) K` with `P.totalDegree ≤ d` that disagrees with
`fun x : rootCube ω n => ∏ i, x.1 i` on at most `e` points of the cube.

**Proof.** Assembles the two halves of the argument.
- `hrepr`: every function on the root cube is represented by a squarefree polynomial, from
  `exists_squarefree_representative_on_rootCube` (two-point Lagrange interpolation).
- `hcounting`: no degree-`≤ n / 2 + d` polynomial `e`-approximates every function on the
  cube — `rootCube_counting_obstruction_lowDegreeSquarefree` at `D := n / 2 + d`, fed `hω1`,
  `hballB`, `hstrict`.
- `exact no_low_degree_rootProd_approx hω0 hrepr hcounting` combines them; that lemma is
  where a degree-`d` approximation of the product is boosted to a degree-`n / 2 + d`
  approximation of an arbitrary function.

**Remark.** The `n / 2 + d` degree budget is the Razborov–Smolensky degree-doubling step;
`hω0` is needed only by the algebraic reduction, `hω1` only by the counting side.
