<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.nonempty_switchingTrace_of_decisionTreeDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Trace from Decision-Tree Depth

**Claim.** If the decision-tree depth of the restriction of the function represented by the DNF is at least $k+1$, then there exists a switching trace for the formula relative to the restriction with parameter $k+1$.

**Proof.** The proof transfers the depth bound to the canonical block decision tree: the decision-tree depth is at most the depth of that tree (by `decisionTreeDepth_le_canonicalBlockTree_depth`), and its depth agrees with that of the auxiliary tree at fuel $n$. The auxiliary-tree result then gives the required switching trace (by `nonempty_switchingTrace_of_depth_canonicalBlockTreeAux`).

**Key facts.** `FABL.DNFFormula.decisionTreeDepth_le_canonicalBlockTree_depth`, `FABL.DNFFormula.nonempty_switchingTrace_of_depth_canonicalBlockTreeAux`.
