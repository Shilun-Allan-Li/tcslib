<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.eval_eq_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation depends on queried coordinates

**Claim.** If two inputs agree on every coordinate available to a finite decision tree, the tree evaluates to the same output on both inputs.

**Proof.** Proceed by induction on the tree. At a leaf, both evaluations are its stored label. At a query of coordinate $i$, availability gives $x_i=y_i$, so both inputs select the same child, namely the child indexed by that common symbol. The remaining available coordinates are those of the original set with $i$ removed. Every such coordinate was available originally, so $x$ and $y$ still agree on all of them. The induction hypothesis applied to the selected child therefore gives equal evaluations.
