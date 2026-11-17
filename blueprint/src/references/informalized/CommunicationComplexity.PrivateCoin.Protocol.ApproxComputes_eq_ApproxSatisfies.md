<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean :: CommunicationComplexity.PrivateCoin.Protocol.ApproxComputes_eq_ApproxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate Computation as Predicate Satisfaction

**Claim.** Approximate computation of $f$ within error $\varepsilon$ is equivalent to approximate satisfaction of the predicate that the output equals $f(x,y)$.

**Proof.** Unfold both definitions. For each fixed input pair $(x,y)$, the failure condition for approximate computation is that the protocol’s output differs from $f(x,y)$. The failure condition for the equality predicate is the negation of the assertion that the output equals $f(x,y)$, which is exactly the same condition. Thus the measured failure sets, and hence their error bounds for every input pair, coincide.
