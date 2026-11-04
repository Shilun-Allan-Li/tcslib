<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSquarefreePolynomial_totalDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The constructed polynomial really has total degree at most `D`

**Claim.** For every `c : LowDegreeSupport n D → K`,
`(lowDegreeSquarefreePolynomial c).totalDegree ≤ D`.

**Proof.** `unfold lowDegreeSquarefreePolynomial` and apply
`MvPolynomial.totalDegree_finsetSum_le`: it suffices to bound the degree of each summand by
`D`. Fix `s` and `by_cases hsD : s.card ≤ D`.

* Low-degree branch: a `calc` chain.
  - `simp [hsD]` discharges the `dite`, leaving `(C (c ⟨s, hsD⟩) * squarefreeMonomial s).totalDegree`.
  - `MvPolynomial.totalDegree_mul` bounds it by the sum of the two factors' degrees.
  - `squarefreeMonomial_totalDegree_le_card` gives `(squarefreeMonomial s).totalDegree ≤ s.card`,
    and `Nat.add_le_add_left` combined with `simpa` uses `(C a).totalDegree = 0`, giving
    `≤ 0 + s.card`.
  - `simpa using hsD` finishes with `s.card ≤ D`.
* Otherwise the summand is `0`, handled by `simp [hsD]`.

**Used in.** The counting obstruction `rootCube_counting_obstruction_lowDegreeSquarefree`,
where the constructed representative must be a legitimate degree-`≤ D` polynomial.
