<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.extractF₂Pivot_coefficient_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of an Extracted Pivot

**Claim.** Whenever pivot extraction at a chosen variable returns an equation, that equation has coefficient $1$ at the chosen variable.

**Proof.** Induct on the list of equations. The empty list cannot produce a pivot. For a nonempty list, inspect its first equation. If its coefficient at the chosen variable is $1$, extraction returns that equation immediately, so the claim follows. Otherwise extraction must recurse on the tail. If that recursive search returns no pivot, the original extraction cannot have returned one. If it returns a pivot and a remainder, the original extraction returns the same pivot, merely retaining the first equation in the remainder. The induction hypothesis says that this pivot has coefficient $1$ at the chosen variable, as required.
