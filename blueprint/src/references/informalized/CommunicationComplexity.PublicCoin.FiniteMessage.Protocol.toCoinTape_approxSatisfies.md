<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinApproximation.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate satisfaction after coin-tape conversion

**Claim.** If the failure probability of the original protocol is at most $\varepsilon$ on every input pair, then the coin-tape protocol obtained with slack $\delta>0$ has failure probability at most $\varepsilon+\delta$ on every input pair.

**Proof.** Fix inputs $x,y$. Let $S$ be the set of shared-randomness outcomes on which the original protocol fails the predicate. The converted protocol uses a map $\phi$ from coin tapes to shared-randomness outcomes, so its failure set is exactly $\phi^{-1}(S)$: this follows from the execution formula for a protocol pulled back along input maps (`comap_run`). The single-coin approximation result (`single_coin_approx`) bounds the measure of this preimage by the measure of $S$ plus $\delta$. The assumed error bound gives $\operatorname{volume}(S)\leq\varepsilon$, hence the converted failure probability is at most $\varepsilon+\delta$.

**Key facts.** `CommunicationComplexity.Internal.single_coin_approx`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
