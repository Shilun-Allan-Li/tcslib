<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation as satisfaction of equality

**Claim.** For every public-coin finite-message protocol, function $f$, and real error bound, the assertion that the protocol computes $f$ within that error equals the assertion that it approximately satisfies the predicate requiring its output to equal $f(x,y)$.

**Proof.** For each input pair and shared coin outcome, failure of the equality predicate means precisely that the protocol's output differs from $f(x,y)$. Consequently the two definitions use the same failure event and impose the same measure bound for every input pair, so the resulting propositions are equal.
