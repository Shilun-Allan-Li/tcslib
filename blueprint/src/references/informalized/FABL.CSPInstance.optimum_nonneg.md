<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.optimum_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Is Nonnegative

**Claim.** The optimum value of the finite constraint satisfaction instance is nonnegative.

**Proof.** The optimum is the value attained by the selected optimal assignment. Every assignment has nonnegative value (`value_nonneg`), so applying that fact to the optimal assignment gives the result.

**Key facts.** `FABL.CSPInstance.value_nonneg`.
