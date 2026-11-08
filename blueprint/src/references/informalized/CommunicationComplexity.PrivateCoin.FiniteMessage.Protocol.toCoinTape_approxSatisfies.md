<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate Correctness of Coin-Tape Conversion

**Claim.** If $p$ fails its predicate with probability at most $\varepsilon$ on every input pair, then its coin-tape conversion at tolerance $\delta>0$ fails with probability at most $\varepsilon+\delta$.

**Proof.** Fix inputs $x,y$. The coin-tape conversion supplies maps from Alice’s and Bob’s fair coin tapes into their original randomness spaces. Let $S$ be the set of original coin pairs on which $p$ fails the predicate at $(x,y)$. The change-of-input execution identity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`) shows that failure for the converted protocol occurs exactly when the mapped coin pair lies in $S$. Hence its failure set is the preimage of $S$ under the product of the two coin maps. The approximation property of those maps, furnished by `CommunicationComplexity.Internal.product_coin_approx`, bounds the measure of this preimage by the measure of $S$ plus $\delta$. The assumed approximate correctness bounds the measure of $S$ by $\varepsilon$, so the converted failure probability is at most $\varepsilon+\delta$.

**Key facts.** `CommunicationComplexity.Internal.product_coin_approx`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
