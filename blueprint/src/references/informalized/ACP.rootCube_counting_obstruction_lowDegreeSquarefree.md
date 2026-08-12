<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: rootCube_counting_obstruction_lowDegreeSquarefree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concrete counting obstruction to low-degree approximation on the root cube

**Claim.** Let `K` be a finite field, `ω ≠ 1`, and `n D e B : ℕ`. Assume
`∑ t ∈ range (e + 1), (2 ^ n).choose t * (Fintype.card K) ^ t ≤ B` (every radius-`e` ball has
size at most `B`) and the strict inequality
`Fintype.card K ^ (2 ^ n) > Fintype.card (LowDegreeSupport n D → K) * B`. Then it is **not**
the case that every `f : rootCube ω n → K` admits a `Q : MvPolynomial (Fin n) K` with
`Q.totalDegree ≤ D` and `rootCubeBadCount f Q ≤ e`.

**Proof.** The three hypotheses of the abstract `rootCube_counting_obstruction` are supplied
with candidate family `Cand := LowDegreeSupport n D → K` and
`poly := lowDegreeSquarefreePolynomial`.
- `hcomplete`: every degree-`≤ D` polynomial agrees on the cube with some member of the
  candidate family — exactly `lowDegree_squarefree_complete_on_rootCube`.
- `hball`: each candidate's radius-`e` ball has at most `B` elements. From
  `rootCubeBall_card_le_binomial` and `hcubeF : Fintype.card (rootCube ω n) = 2 ^ n`
  (`rootCube_card_of_ne_one`), a `Finset.sum_congr` with
  `simp [Nat.card_eq_fintype_card, hcubeF]` rewrites the bound's right-hand side into the
  `2 ^ n` form, and `le_trans` with `hballB` gives `≤ B`.
- `hstrict'`: `Nat.card (rootCube ω n → K) > Fintype.card (LowDegreeSupport n D → K) * B`,
  obtained from `rootCube_function_card_of_ne_one` (rewriting the left side as
  `Fintype.card K ^ (2 ^ n)`) plus `hstrict`.
- `exact rootCube_counting_obstruction … hcomplete hball hstrict'` concludes.

**Remark.** This is the concrete instantiation step: the pigeonhole is entirely in the
abstract lemma, and the work here is matching the explicit squarefree family to its
interface.
