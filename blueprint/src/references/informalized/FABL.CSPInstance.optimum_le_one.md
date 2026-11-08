<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.optimum_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Is at Most One

**Claim.** The optimum value of the finite constraint satisfaction instance is at most one.

**Proof.** The optimum is the value attained by the selected optimal assignment. Every assignment has value at most one (`value_le_one`), so applying that bound to the optimal assignment proves the claim.

**Key facts.** `FABL.CSPInstance.value_le_one`.
