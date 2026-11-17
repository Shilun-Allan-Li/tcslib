<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.assignment_eq_none_of_not_mem_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unqueried Coordinates Are Unset

**Claim.** For a path on $n$ binary coordinates, any coordinate outside its support is assigned `none`.

**Proof.** Membership in the support is equivalent to having an assignment different from `none` (`FABL.F₂DecisionTree.Path.mem_support`). If a coordinate outside the support were assigned a value, that characterization would put it in the support, contradicting the assumption. Hence its assignment is `none`.

**Key facts.** `FABL.F₂DecisionTree.Path.mem_support`.
