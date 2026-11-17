<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Recursive Tree

**Claim.** For every $d\in\mathbb{N}$ and every random seed at level $d$, the resulting deterministic decision tree computes the recursively defined NAND function on inputs in $\{\pm1\}^{2^d}$.

**Proof.** Proceed by induction on $d$. At level zero, the tree queries the sole input coordinate and returns its value, so it computes the level-zero function (`recursiveNandIdentityTree_computes`). For the induction step, write the seed as an order choice together with seeds for the left and right subtrees. Fix an input. The evaluation of the final tree is unaffected by the changes of available-coordinate sets (`FiniteDecisionTree.eval_castAvailable`). Each embedded subtree evaluates as its original tree on the corresponding input block (`eval_recursiveNandTreeInBlock`), and the induction hypothesis identifies those evaluations with the recursive NAND values of the two blocks. The ordered composition evaluates to the NAND of the first subtree's value and the continuation on the second (`eval_orderedNandTree`). If the order choice is zero, the left subtree is evaluated first; if it is not zero, the right subtree is evaluated first. In the latter case, the proof checks the four possibilities for whether each block value is $1$ or $-1$. In both orders, the continuation returns $1$ precisely when both block values are $-1$, and returns $-1$ otherwise. This is exactly the defining rule for the recursive NAND function, completing the induction.

**Key facts.** `FABL.recursiveNandIdentityTree_computes`, `FABL.FiniteDecisionTree.eval_castAvailable`, `FABL.eval_orderedNandTree`, `FABL.eval_recursiveNandTreeInBlock`.
