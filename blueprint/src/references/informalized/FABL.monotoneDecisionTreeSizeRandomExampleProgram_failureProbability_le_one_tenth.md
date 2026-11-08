<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.monotoneDecisionTreeSizeRandomExampleProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision-Tree Learning Failure Bound

**Claim.** For a monotone Boolean function whose deterministic decision-tree size is at most $n^d$, the probability that the decision-tree-size random-example program outputs a hypothesis at relative Hamming distance greater than $\varepsilon$ is at most $1/10$.

**Proof.** The deterministic decision-tree-size hypothesis gives an upper bound on the target's total influence by the decision-tree-size influence bound (`totalInfluence_le_decisionTreeSizeInfluenceBound`). Use that bound as the influence hypothesis in the general failure-probability theorem for the monotone bounded-influence random-example program. Its conclusion is precisely the claimed error probability, and the program becomes the decision-tree-size program when the influence parameter is so instantiated (`monotoneBoundedInfluenceRandomExampleProgram_failureProbability_le_one_tenth`).

**Key facts.** `FABL.totalInfluence_le_decisionTreeSizeInfluenceBound`, `FABL.monotoneBoundedInfluenceRandomExampleProgram_failureProbability_le_one_tenth`.
