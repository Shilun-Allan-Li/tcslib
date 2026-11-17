<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.recursiveNAND_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND Depth Lower Bound

**Claim.** For every natural number $d$, any finite decision tree on the $2^d$-dimensional sign cube that computes the recursively defined NAND function has depth at least $2^d$.

**Proof.** Convert the sign-valued tree into its corresponding binary-input, real-valued decision tree. Since the original tree computes recursive NAND, the conversion theorem (`toF₂Real_computes`) shows that this tree computes the real-valued version of recursive NAND. The Fourier-degree lower bound for decision trees (`fourierDegree_toReal_le_depth_of_decisionTree`) therefore gives that the Fourier degree of this function is at most the converted tree's depth. The recursive NAND degree formula (`fourierDegree_recursiveNAND`) identifies that degree as $2^d$, while `depth_toF₂Real_le` says conversion does not increase depth. Combining these inequalities yields $2^d\leq T.\mathrm{depth}$.

**Key facts.** `FABL.FiniteDecisionTree.toF₂Real_computes`, `FABL.fourierDegree_toReal_le_depth_of_decisionTree`, `FABL.fourierDegree_recursiveNAND`, `FABL.FiniteDecisionTree.depth_toF₂Real_le`.
