<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSquarefreePolynomial_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Zero coefficients give the zero polynomial

**Claim.** `lowDegreeSquarefreePolynomial (fun _ : LowDegreeSupport n D => (0 : K)) = 0`.

**Proof.** `unfold lowDegreeSquarefreePolynomial`, then `Finset.sum_eq_zero`: it suffices
that each summand vanishes. For a fixed `s`, `by_cases hsD : s.card ≤ D <;> simp [hsD]` —
in the `true` branch the summand is `MvPolynomial.C 0 * squarefreeMonomial s = 0`, and in
the `false` branch the `dite` already returns `0`.

**Used in.** The base case of `lowDegreeSquarefreePolynomial_sum`.
