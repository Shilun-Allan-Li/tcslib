<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPGaps.lean :: FABL.PCPPDescription.optimumAcceptance_eq_one_of_satisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiable Instance Has Acceptance One

**Claim.** If the circuit is satisfiable, the PCPP system's optimum acceptance probability is $1$.

**Proof.** Choose a satisfying input word for the circuit. By the completeness condition in the PCPP guarantee, there is a proof word for which the verifier accepts with probability exactly $1$. Since the optimum is at least the acceptance probability on every particular input-proof pair (`acceptanceProbability_le_optimumAcceptance`), the optimum is at least $1$. On the other hand, every acceptance probability, including the optimum, is at most $1$ (`optimumAcceptance_le_one`). These two bounds imply that the optimum equals $1$.

**Key facts.** `FABL.PCPPSystem.acceptanceProbability_le_optimumAcceptance`, `FABL.PCPPSystem.optimumAcceptance_le_one`.
