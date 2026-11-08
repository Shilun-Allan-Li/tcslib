<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.eval_completeTreeAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Partial Complete Tree

**Claim.** If the partial input agrees with $x$ outside the available coordinates, then the partial complete tree evaluates at $x$ to $f(x)$.

**Proof.** Use induction on the number of available coordinates, following the recursive construction. If the available set is nonempty, let $i$ be the coordinate selected by the construction. When $x_i=0$, evaluation follows the zero-child, whose partial input is updated to $0$ at $i$ and whose available set has removed $i$. These data still agree with $x$ outside the remaining available set: at $i$ they agree by the branch choice, and at every other coordinate outside that set they agree by the original hypothesis. The induction hypothesis gives output $f(x)$. When $x_i=1$, the one-child and its update to $1$ give the same conclusion. If the available set is empty, the construction returns $f$ of the partial input. The agreement hypothesis now says the partial input equals $x$ at every coordinate, so this output is $f(x)$.
