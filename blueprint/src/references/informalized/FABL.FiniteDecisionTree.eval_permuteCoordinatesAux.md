<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.eval_permuteCoordinatesAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under coordinate permutation

**Claim.** For a tree with available coordinates $A$, permuting its coordinates by $\sigma$ and evaluating at $x$ gives the same output as evaluating the original tree at the input $i\mapsto x_{\sigma(i)}$.

**Proof.** Proceed by induction on the tree. At a leaf, both evaluations return its label. At a query of coordinate $i$, the permuted tree queries $\sigma(i)$, so at input $x$ it selects the child indexed by $x_{\sigma(i)}$. That child is the coordinate-permuted version of the corresponding original child, with its available set identified using the equality between permuting an erased set and erasing the permuted coordinate. The cast across this equality does not change evaluation, by the fact that changing only the available-set index along an equality preserves evaluation (\texttt{FABL.FiniteDecisionTree.eval\_castAvailable}). The induction hypothesis for the selected child, evaluated at $x_{\sigma(i)}$, now gives the desired equality.

**Key facts.** `FABL.FiniteDecisionTree.eval_castAvailable`.
