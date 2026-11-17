<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.mem_support_withQuery_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support after a query

**Claim.** After assigning a bit at coordinate $i$, a coordinate $j$ belongs to the resulting support exactly when $j=i$ or $j$ was already in the original support.

**Proof.** If $j=i$, the updated assignment at that coordinate is the chosen bit, hence is not `none`, so $j$ is in the new support. If $j\ne i$, updating the assignment leaves its value at $j$ unchanged; therefore it is non-`none` after the update exactly when it was non-`none` before. By the definition of support, this is precisely the stated equivalence.
