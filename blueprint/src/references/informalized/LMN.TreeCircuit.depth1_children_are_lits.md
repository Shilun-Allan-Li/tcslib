<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: LMN.TreeCircuit.depth1_children_are_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depths below a shallow gate

**Claim.** If a gate applied to a list of circuit trees has depth at most $1$, then every child in the list has depth $0$.

**Proof.** Expanding the depth of the gate shows that one plus the maximum depth accumulated over its children is at most $1$. Thus that accumulated maximum is $0$. For any child, its depth is bounded by this maximum: in the fold over the list, each entry is bounded by the maximum of that entry and the remaining fold. Hence each child has depth at most $0$, and natural-number depths are nonnegative, so each is exactly $0$.
