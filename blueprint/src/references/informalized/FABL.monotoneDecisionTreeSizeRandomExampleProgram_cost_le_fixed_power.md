<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.monotoneDecisionTreeSizeRandomExampleProgram_cost_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Cost Bound

**Claim.** Under the precision assumption, every supported outcome of the decision-tree-size random-example program has the stated polynomial bounds on random examples and work, and makes no membership queries.

**Proof.** First, the decision-tree-size influence bound satisfies the sub-square-root regime required by the general cost theorem: the assumed $n\ge 1$ and $1/(Q+1)\le\varepsilon$ give this directly (the decision-tree sub-square-root regime criterion, `decisionTreeSizeInfluenceBound_subsqrtRegime`). The program in the claim is exactly the bounded-influence random-example program instantiated with this influence bound. Applying the general cost theorem for that program to the given supported outcome yields the three bounds, with regime parameters $C=d+1$ and $Q$ (`monotoneBoundedInfluenceRandomExampleProgram_cost_le_fixed_power`).

**Key facts.** `FABL.decisionTreeSizeInfluenceBound_subsqrtRegime`, `FABL.monotoneBoundedInfluenceRandomExampleProgram_cost_le_fixed_power`.
