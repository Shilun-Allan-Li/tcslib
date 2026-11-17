<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.support_withQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support after assigning a coordinate

**Claim.** After assigning a bit at coordinate $i$, the path's support is the original support with $i$ inserted.

**Proof.** Two finite sets are equal once their membership conditions agree at every coordinate $j$. By the support membership characterization after a query (`FABL.F₂DecisionTree.Path.mem_support_withQuery_iff`), membership in the updated support means $j=i$ or $j$ belongs to the original support. This is exactly the membership condition for the original support with $i$ inserted.

**Key facts.** `FABL.F₂DecisionTree.Path.mem_support_withQuery_iff`.
