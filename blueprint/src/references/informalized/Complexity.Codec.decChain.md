<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean :: Complexity.Codec.decChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Decrement Execution

**Claim.** If each of the first $k$ labels decrements register $r$ and continues to the next label, every initial register is at most $B$, and register $r$ initially has value at least $k$, then there is a finite guarded execution from label $\ell_0$ to $\ell_k$. It reduces register $r$ by $k$, preserves all other registers, and keeps every earlier configuration safe with all registers bounded by $B$.

**Proof.** Apply the repeated single-register update theorem `arm_chain` with the decrement direction. Its instruction hypothesis is exactly the given condition on the labels, and its required bound condition in the decrement case is $k\leq v(r)$, which is assumed. The theorem therefore provides a finite execution with register $r$ changed to $v(r)-k$, every other register unchanged, and the guard and register bound holding at each configuration before the endpoint.

**Key facts.** `Complexity.LogProg.arm_chain`.
