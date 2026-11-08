<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.eval_node_false_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Evaluation of an OR Node

**Claim.** An OR node evaluates to true if and only if at least one of its children evaluates to true.

**Proof.** Unfold the evaluation of the OR node, which is the right fold of Boolean disjunction starting from false, and induct on the child list. For the empty list, the fold is false and there is no child witnessing a true value, so both sides of the equivalence are false. For a list with head child $c$ and tail $cs$, the fold is $c.eval\,x$ OR the fold for $cs$. It is true exactly when $c.eval\,x$ is true or some child in the tail evaluates to true; by the induction hypothesis this is equivalent to the existence of a child in the full list evaluating to true.
