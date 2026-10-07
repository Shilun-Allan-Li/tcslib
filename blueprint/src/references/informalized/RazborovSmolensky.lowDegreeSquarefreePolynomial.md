<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSquarefreePolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A degree-`≤ D` squarefree polynomial from its coefficients

**Definition.** Given `c : LowDegreeSupport n D → K`,
`lowDegreeSquarefreePolynomial c : MvPolynomial (Fin n) K` is the sum over *all* subsets
`s : Finset (Fin n)` of

`if hs : s.card ≤ D then MvPolynomial.C (c ⟨s, hs⟩) * squarefreeMonomial s else 0`.

So the terms with `s.card ≤ D` contribute `c ⟨s, hs⟩ · ∏ i ∈ s, X i` and all larger
supports contribute `0`. The `dite` lets the sum range over `Finset.univ : Finset (Finset (Fin n))`
while only the low-degree part of the index carries a coefficient.

**Remark.** This is the degree-truncated companion of `squarefreePolynomial`, which takes an
unrestricted coefficient function `Finset (Fin n) → K`. The construction is `noncomputable`
and opens with `classical` to get decidability of `s.card ≤ D` for the `dite`. Its basic
properties are `lowDegreeSquarefreePolynomial_zero`, `_add`, `_sum` (additivity in `c`) and
`_totalDegree_le` (degree at most `D`).
