<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.F₂DecisionTree.hasCNFWidthLE_decisionTreeDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF Width from Decision-Tree Depth

**Claim.** Every Boolean function has a CNF of width at most the decision-tree depth of its binary encoding.

**Proof.** Let $g$ be the Boolean dual of the given function $f$. Encoding the dual amounts to taking the binary Boolean dual of the encoding of $f$: this follows coordinatewise from the fact that complementing a binary coordinate negates its sign encoding (`signEncode_binaryCubeComplement`). The binary Boolean dual preserves decision-tree depth (`decisionTreeDepth_binaryBooleanDual`), so $g$ and $f$ have the same relevant depth. The DNF width bound supplies a DNF for $g$ whose width is at most that depth (`hasDNFWidthLE_decisionTreeDepth`). Form a CNF whose clauses are the terms of this DNF; its width is the same maximum term width. Switching conjunctions and disjunctions shows that the Boolean dual of this CNF's function is the function of the supplied DNF (`switchAndOr_toBooleanFunction`). That DNF computes $g$, which is the dual of $f$. Since Boolean duality is injective (`booleanDual_injective`), the constructed CNF computes $f$, with the required width bound.

**Key facts.** `FABL.signEncode_binaryCubeComplement`, `FABL.decisionTreeDepth_binaryBooleanDual`, `FABL.F₂DecisionTree.hasDNFWidthLE_decisionTreeDepth`, `FABL.CNFFormula.switchAndOr_toBooleanFunction`, `FABL.booleanDual_injective`.
