<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.deterministicDepth_recursiveNAND_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Recursive NAND Depth

**Claim.** For every $d$, the minimum worst-case deterministic decision-tree depth for recursive NAND on $2^d$ inputs is at most $2^d$.

**Proof.** Take a tree computing recursive NAND whose depth equals the minimum, using `exists_computingTree_depth_eq_deterministicDepth`. A decision tree's depth is at most the number of available coordinates, by `depth_le_dimension`. Here that number is $2^d$, so the minimum depth is at most $2^d$.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth`, `FABL.FiniteDecisionTree.depth_le_dimension`.
