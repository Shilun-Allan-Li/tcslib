<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.derandomizedBLRProgram_cost_eq_of_mem_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of supported outcomes

**Claim.** Every outcome in the support of the program’s run distribution has cost $(0,3,n+r+(2n+1)+3)$.

**Proof.** The run distribution is the pushforward of the uniform distribution on pairs of input bits and seed bits, with each pair mapped to the program’s Boolean result together with the fixed cost `derandomizedBLRCost n r` (`runWithCost_derandomizedBLRProgram`). Membership in the support of a pushforward implies that the outcome is the image of some input pair. Its cost component is therefore the fixed cost, as claimed.

**Key facts.** `FABL.runWithCost_derandomizedBLRProgram`.
