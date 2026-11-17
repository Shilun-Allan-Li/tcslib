<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.toClauses_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause representation preserves evaluation

**Claim.** For every decision tree $T$ and Boolean input $x$, the conjunction of the clauses produced from $T$ evaluates to the same Boolean value as $T$ on $x$.

**Proof.** Proceed by induction on the tree. At a true leaf, the clause list is empty, so its conjunction is true, matching the leaf; at a false leaf, the list contains the empty clause, whose disjunction is false, matching that leaf. At a branch on variable $v$, the clause list consists of clauses from the low subtree prefixed by the literal asserting $v=0$, followed by clauses from the high subtree prefixed by the literal asserting $v=1$. If $x(v)=0$, every prefixed high-subtree clause is automatically true, while the low-subtree clauses evaluate as their original clauses; thus the total conjunction equals the low subtree's value by induction. If $x(v)=1$, the low-subtree prefixed clauses are automatically true and the high-subtree clauses determine the conjunction, which equals the high subtree's value. These are exactly the two evaluations of the decision tree at its branch.

**Key facts.** `Clause.eval_cons`.
