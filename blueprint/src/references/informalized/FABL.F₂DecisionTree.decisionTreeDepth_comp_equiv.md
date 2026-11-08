<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.decisionTreeDepth_comp_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under coordinate equivalence

**Claim.** Composing a function on one binary cube with a bijection of coordinates preserves its decision tree depth.

**Proof.** A coordinate equivalence is, in particular, an injective coordinate embedding. Apply the depth-preservation result for embeddings (`decisionTreeDepth_comp_embedding`) to its underlying embedding.

**Key facts.** `FABL.F₂DecisionTree.decisionTreeDepth_comp_embedding`.
