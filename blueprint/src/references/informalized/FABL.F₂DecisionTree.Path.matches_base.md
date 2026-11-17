<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.matches_base -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The base point matches the path

**Claim.** The point that takes each assigned value at specified coordinates and takes $0$ elsewhere matches the path.

**Proof.** Matching is equivalent to agreeing with the base point at every coordinate in the path's support (`matches_iff_forall_mem_support_eq_base`). For each such coordinate, the path assignment is defined, and the base point is precisely that assigned value. Thus the required agreement holds at every supported coordinate.

**Key facts.** `FABL.F₂DecisionTree.Path.matches_iff_forall_mem_support_eq_base`.
