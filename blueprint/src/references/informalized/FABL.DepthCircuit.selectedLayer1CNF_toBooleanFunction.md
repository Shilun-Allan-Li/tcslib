<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.selectedLayer1CNF_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Clauses Compute the Next OR Layer

**Claim.** If the first-layer gates are OR gates, the CNF formula made from any selected first-layer terms computes the same Boolean function as the dual next-layer gate applied to those selected outputs.

**Proof.** Fix an input. The selected CNF evaluates to $-1$ exactly when every selected clause evaluates to $-1$. Each such clause evaluates to $-1$ exactly when at least one of its literals evaluates to $-1$. Because the first-layer gates are OR gates, this clause value is exactly the corresponding first-layer output; and because the dual of OR is AND, requiring every selected output to be $-1$ is exactly the next-layer gate's evaluation on those indices. Thus the two functions agree on whether their values are $-1$. Both values are signs, so each is either $-1$ or $1$; agreement on being $-1$ implies equality.
