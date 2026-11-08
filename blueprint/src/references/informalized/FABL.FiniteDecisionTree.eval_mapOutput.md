<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.eval_mapOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation commutes with output relabeling

**Claim.** Applying a function $g$ to every output label of a finite decision tree and then evaluating it gives the same result as evaluating the original tree and applying $g$ to its output.

**Proof.** Proceed by induction on the tree. At a leaf, relabeling changes its stored value $a$ to $g(a)$, which is exactly the result of applying $g$ to the original evaluation. At a query of coordinate $i$, both the relabeled tree and the original tree choose the child indexed by the input symbol $x_i$. The induction hypothesis for that child says its relabeled evaluation is $g$ of its original evaluation, proving the claim.
