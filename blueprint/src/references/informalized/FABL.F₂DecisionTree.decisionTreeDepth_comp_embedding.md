<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.decisionTreeDepth_comp_embedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under coordinate embedding

**Claim.** Composing a function on the smaller binary cube with an injective coordinate embedding preserves its decision tree depth.

**Proof.** First choose a tree $T$ computing the original function whose depth is its minimum possible depth (`exists_computingTree_depth_eq_decisionTreeDepth`). Push its queries along the coordinate embedding. The evaluation correspondence for pushed trees (`eval_pushEmbedding`) shows that the resulting tree computes the composed function; the pointwise computation characterization (`computes_iff`) expresses this as equality at each input. Its depth is unchanged (`depth_pushEmbedding`). Since the decision tree depth is no greater than the depth of any computing tree (`decisionTreeDepth_le_of_computes`), this proves that the composed function's depth is at most the original depth.

For the reverse inequality, choose a minimum-depth tree $T$ for the composed function. Pull its queries back along the embedding. The evaluation correspondence for pulled trees (`eval_pullEmbedding`) evaluates the original tree on the extension of a smaller-cube input by zeros. Because the embedding is injective, that extension agrees with the input on every embedded coordinate; the computation hypothesis therefore shows that the pulled tree computes the original function. Its depth is at most that of $T$ (`depth_pullEmbedding_le`). Applying the minimum-depth bound (`decisionTreeDepth_le_of_computes`) gives the reverse inequality, and hence equality.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`, `FABL.F₂DecisionTree.eval_pushEmbedding`, `FABL.F₂DecisionTree.computes_iff`, `FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes`, `FABL.F₂DecisionTree.depth_pushEmbedding`, `FABL.F₂DecisionTree.eval_pullEmbedding`, `FABL.F₂DecisionTree.depth_pullEmbedding_le`.
