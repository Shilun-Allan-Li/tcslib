<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.abs_expectRandomRestriction_le_expect_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Expectation Under Random Restriction

**Claim.** When $0\le\delta\le1$, the absolute value of the random-restriction expectation of $g$ is at most the random-restriction expectation of $|g|$.

**Proof.** Expand the expectation as a finite sum over coordinate subsets $J$. The absolute value of this sum is at most the sum of the absolute values of its terms. Each weight $\delta^{|J|}(1-\delta)^{n-|J|}$ is nonnegative (`deltaRandomSubsetWeight_nonneg`), so the absolute value of a weighted term equals the weight times the absolute value of the corresponding expectation. For each $J$, the absolute value of an expectation is at most the expectation of the absolute value. Multiplying this inequality by the nonnegative weight and summing over $J$ gives the claimed bound.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`.
