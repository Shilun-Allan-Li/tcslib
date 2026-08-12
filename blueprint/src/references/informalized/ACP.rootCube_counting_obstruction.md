<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCube_counting_obstruction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting obstruction to low-degree approximation on `{1, ω}^n`

**Claim.** Fix a finite field `K`, `n D e B : ℕ` and a finite candidate type `Cand` with
`poly : Cand → MvPolynomial (Fin n) K`. Assume: (i) `hcomplete` — every `Q` of total degree
`≤ D` agrees on the cube with some candidate `poly c`; (ii) `hball` — each Hamming ball
`rootCubeBall (fun x => (poly c).eval x.1) e` has at most `B` elements; (iii) `hstrict` —
`Nat.card (rootCube ω n → K) > Fintype.card Cand * B`. Then it is *not* the case that every
`f : rootCube ω n → K` has a `Q` with `Q.totalDegree ≤ D` and
`rootCubeBadCount f Q ≤ e`.

**Proof.** Assume such a `Q` exists for every `f` (`intro hcover`), after installing
`Fintype K` from `Fintype.ofFinite`, `Classical.decEq`, and the induced `Fintype` on the
function space.

1. `hball'`: restate (ii) as a bound on `Finset.filter` cardinalities, by
   `simpa [rootCubeBall, rootCubeFunctionBadCount]`.
2. `hcover'`: for each `f`, take the approximant `Q` from `hcover` and the candidate `c`
   from `hcomplete Q`. Since `poly c` and `Q` agree pointwise on the cube (`hc`), the two
   bad-point sets are equal — `congrArg Finset.card` after `ext x; simp [hc x]` — so the
   candidate inherits the bound `≤ e`.
3. `finite_cover_by_hamming_balls_card_bound` with `center c x = (poly c).eval x.1` turns
   the cover plus ball bound into `Fintype.card (rootCube ω n → K) ≤ Fintype.card Cand * B`.
4. `simpa [Nat.card_eq_fintype_card]` converts to `Nat.card`, and `not_lt_of_ge` contradicts
   `hstrict`.

**Remark.** The statement is deliberately parametric in `Cand`, `e`, and `B`: the numerical
entropy/binomial estimate lives entirely in the hypothesis `hstrict`.
