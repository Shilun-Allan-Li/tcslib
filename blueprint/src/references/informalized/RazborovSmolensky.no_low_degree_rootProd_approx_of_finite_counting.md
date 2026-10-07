<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: no_low_degree_rootProd_approx_of_finite_counting -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Same conclusion from an explicit finite candidate family

**Claim.** Fix finite `K`, `ω ≠ 0`, naturals `n d e B`, a `Fintype Cand` and
`poly : Cand → MvPolynomial (Fin n) K`. Assume

- `hrepr`: every function on `rootCube ω n` is computed on the cube by a squarefree
  polynomial;
- `hcomplete`: every `Q` with `Q.totalDegree ≤ n / 2 + d` agrees on the cube with some
  candidate `poly c`;
- `hball`: `(rootCubeBall ω (fun x => (poly c).eval x.1) e).card ≤ B` for every `c`;
- `hstrict`: `Nat.card (rootCube ω n → K) > Fintype.card Cand * B`.

Then no `P` with `P.totalDegree ≤ d` satisfies
`rootCubeBadCount ω (fun x => ∏ i, x.1 i) P ≤ e`.

**Proof.** A single `exact`: feed `rootCube_counting_obstruction` (at `D = n / 2 + d`,
with `poly`, `hcomplete`, `hball`, `hstrict`) as the `hcounting` argument of
`no_low_degree_rootProd_approx`, keeping `hω0` and `hrepr`.

**Remark.** This is the packaging step, not new mathematics: it replaces the abstract
`hcounting` by four checkable finite hypotheses. The intended instantiation names
`Cand` as the coefficient vectors of multilinear polynomials of degree `≤ n / 2 + d`,
with `B` from a binomial/entropy estimate.

**Status.** Proved with no `sorry`, but not yet applied anywhere in the library —
`LowDegreeObstruction.lean` instead calls `no_low_degree_rootProd_approx` directly.
