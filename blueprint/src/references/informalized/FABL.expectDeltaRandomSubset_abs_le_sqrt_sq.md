<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.expectDeltaRandomSubset_abs_le_sqrt_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute expectation and second moment

**Claim.** For $\rho\in[0,1]$, the weighted average of $|g(J)|$ over subsets is at most the square root of the weighted average of $g(J)^2$ with the same weights.

**Proof.** Write $w(J)=\rho^{|J|}(1-\rho)^{n-|J|}$. These weights are nonnegative (by `deltaRandomSubsetWeight_nonneg`) and sum to one (by `sum_deltaRandomSubsetWeight`). Thus $w(J)|g(J)|=\sqrt{w(J)}\,\bigl(\sqrt{w(J)}|g(J)|\bigr)$. Apply the finite Cauchy–Schwarz inequality to the two factors indexed by $J$. The sum of the squares of the first factors is $\sum_Jw(J)=1$, while the sum of squares of the second factors is $\sum_Jw(J)g(J)^2$, using $|g(J)|^2=g(J)^2$. The resulting bound is exactly the claimed inequality.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`, `FABL.sum_deltaRandomSubsetWeight`.
