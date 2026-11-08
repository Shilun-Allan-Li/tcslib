<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.decisionTreeDepth_restrict_compose_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under composed restrictions

**Claim.** Composing the restriction that fixes coordinates outside $J$ with a second coordinate restriction gives a function whose minimum decision tree depth equals that of the reindexed restriction to $J$ followed by the corresponding second restriction.

**Proof.** The restriction composition identity (`FABL.restrict_compose_coordRestrictionOf`) expresses the left-hand restricted function as the function on the full binary cube that evaluates the reindexed restriction using only the coordinates embedded from $J$. Applying invariance of minimum decision tree depth under an injective reindexing of coordinates (`FABL.F₂DecisionTree.decisionTreeDepth_comp_embedding`) gives the asserted equality.

**Key facts.** `FABL.restrict_compose_coordRestrictionOf`, `FABL.F₂DecisionTree.decisionTreeDepth_comp_embedding`.
