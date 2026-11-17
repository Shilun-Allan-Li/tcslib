<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.toTerms_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Term representation preserves evaluation

**Claim.** For every decision tree $T$ and Boolean input $x$, at least one term produced from $T$ evaluates to true exactly when $T$ evaluates to true on $x$.

**Proof.** Proceed by induction on the tree. At a true leaf, the term list contains the empty term, which evaluates to true; at a false leaf, it is empty, so no term evaluates to true. At a branch on variable $v$, the terms from the low subtree are prefixed by the literal asserting $v=1$, and those from the high subtree by the literal asserting $v=0$. If $x(v)=0$, every low-subtree prefixed term fails, while the high-subtree prefixed terms have the same truth values as their original terms; hence some term succeeds exactly when the high subtree evaluates to true. If $x(v)=1$, the high-subtree prefixed terms fail and the low-subtree terms determine whether any term succeeds, exactly as the low subtree evaluates. Thus the disjunction of the produced terms agrees with the tree in either branch case.

**Key facts.** `Term.eval_cons`.
