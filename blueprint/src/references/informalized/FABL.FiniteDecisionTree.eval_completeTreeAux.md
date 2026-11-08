<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.eval_completeTreeAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the completed tree

**Claim.** If a partial input agrees with the given input outside the available set, the tree constructed from the function, partial input, and available set evaluates on that input to the function’s value.

**Proof.** Unfold the recursive construction. If the available set is nonempty, let $j$ be its least element. The tree queries $j$, and on input $x$ continues into the child formed by updating the partial input at $j$ to $x_j$, with $j$ removed from the available set. The updated partial input still agrees with $x$ outside that smaller set: at $j$ this holds by the update, and at any other coordinate outside the smaller set, membership in the original available set would imply membership in the set with $j$ erased. The induction hypothesis for the child therefore gives value $f(x)$. If the available set is empty, the construction returns a leaf labelled by $f$ of the partial input. The partial input agrees with $x$ at every coordinate in this case, so the two inputs are equal and the leaf evaluates to $f(x)$.
