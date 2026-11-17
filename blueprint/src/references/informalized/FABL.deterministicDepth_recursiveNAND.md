<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.deterministicDepth_recursiveNAND -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND Decision-Tree Depth

**Claim.** For every $d$, the minimum deterministic decision-tree depth of recursive NAND on $2^d$ inputs is $2^d$.

**Proof.** The upper bound `deterministicDepth_recursiveNAND_le` gives minimum depth at most $2^d$. For the reverse inequality, choose a tree computing recursive NAND whose depth realizes the minimum; existence is supplied by `exists_computingTree_depth_eq_deterministicDepth`. Every such tree has depth at least $2^d$, by `recursiveNAND_depth_le`. The realizing tree therefore has depth at least $2^d$, and the two bounds give equality.

**Key facts.** `FABL.deterministicDepth_recursiveNAND_le`, `FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth`, `FABL.FiniteDecisionTree.recursiveNAND_depth_le`.
