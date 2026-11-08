<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.eval_node_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Evaluation of an AND Gate

**Claim.** An AND gate evaluates to true if and only if every circuit in its child list evaluates to true.

**Proof.** Unfold the AND-node evaluation, a right fold of conjunction starting from true, and induct on the child list. For the empty list, the fold is true and every child evaluates to true vacuously. For a head child $c$ followed by a tail $cs$, the fold is $c.eval\,x$ AND the fold for $cs$. This is true exactly when $c.eval\,x$ is true and every child in the tail evaluates to true, using the induction hypothesis; that is precisely the condition that every child in the full list evaluates to true.
