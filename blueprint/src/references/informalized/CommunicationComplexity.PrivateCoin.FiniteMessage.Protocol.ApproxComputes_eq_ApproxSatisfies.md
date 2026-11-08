<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation as Equality Satisfaction

**Claim.** For a private-coin protocol, $\varepsilon$-computing $f$ is exactly the same proposition as $\varepsilon$-satisfying the predicate that the output equals $f(x,y)$.

**Proof.** Unfold both definitions. For each pair of inputs, the bad event in approximate computation is that the protocol output differs from $f(x,y)$. The bad event for the equality predicate is the negation of the assertion that the output equals $f(x,y)$; these are the same condition. Thus the measured bad-event bounds, and consequently the two propositions, coincide.
