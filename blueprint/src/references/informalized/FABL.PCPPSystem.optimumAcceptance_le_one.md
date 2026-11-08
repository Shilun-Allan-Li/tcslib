<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPGaps.lean :: FABL.PCPPSystem.optimumAcceptance_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Acceptance Bound

**Claim.** The PCPP system's maximum acceptance probability over all input words and proof words is at most $1$.

**Proof.** The optimum acceptance probability is the verifier's acceptance probability at its selected maximizing input-proof pair. A verifier's acceptance probability is at most $1$ (`NonadaptiveFunctionTester.acceptanceProbability_le_one`); applying this bound to that selected pair proves the claim.

**Key facts.** `FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one`.
