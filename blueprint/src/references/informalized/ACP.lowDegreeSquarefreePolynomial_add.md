<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSquarefreePolynomial_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The constructor is additive in its coefficient function

**Claim.** For `c₁ c₂ : LowDegreeSupport n D → K`,

`lowDegreeSquarefreePolynomial (fun s => c₁ s + c₂ s) = lowDegreeSquarefreePolynomial c₁ + lowDegreeSquarefreePolynomial c₂`.

**Proof.** Three steps.

1. `unfold lowDegreeSquarefreePolynomial` on both sides.
2. `rw [← Finset.sum_add_distrib]` merges the two right-hand sums into one sum over
   `Finset (Fin n)`, so `Finset.sum_congr rfl` reduces the goal to a per-support identity.
3. For a fixed `s`, `by_cases hsD : s.card ≤ D`. In the low-degree branch
   `simp [hsD, add_mul]` uses `MvPolynomial.C (a + b) = C a + C b` and distributivity over
   `squarefreeMonomial s`; in the other branch `simp [hsD]` reduces both sides to `0 + 0`.

**Used in.** `lowDegreeSquarefreePolynomial_sum` (the `insert` step).
