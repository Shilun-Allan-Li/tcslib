<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.monotoneDecisionTreeSizeRandomExampleProgram_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision-Tree Program Cost Bounds

**Claim.** For any target, decision-tree parameter, accuracy, and supported outcome of the monotone decision-tree-size random-example program, the outcome's random-example count and work are bounded by the corresponding monotone bounded-influence budgets, and its membership-query count is zero.

**Proof.** By definition, the decision-tree-size program is the monotone bounded-influence program with influence parameter `decisionTreeSizeInfluenceBound n d`. Rewriting the support condition using this definition lets us apply the monotone bounded-influence program cost theorem (`monotoneBoundedInfluenceRandomExampleProgram_cost_le`) directly. It supplies the claimed example, query, and work bounds with that substituted parameter.

**Key facts.** `FABL.monotoneBoundedInfluenceRandomExampleProgram_cost_le`.
