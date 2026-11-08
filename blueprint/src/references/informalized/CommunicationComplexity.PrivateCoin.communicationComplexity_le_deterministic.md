<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.PrivateCoin.communicationComplexity_le_deterministic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic protocols bound randomized complexity

**Claim.** For every function $f$ and every nonnegative error parameter $\varepsilon$, its private-coin randomized communication complexity is at most its deterministic communication complexity.

**Proof.** If the deterministic complexity is infinite, the inequality holds because every extended natural number is at most infinity. Otherwise, write the deterministic complexity as $n$. The deterministic complexity characterization provides a deterministic protocol computing $f$ with cost at most $n$. Convert it to an equivalent finite-message protocol, preserving both its run and its complexity. Use this protocol with zero-length coin tapes for both players, so its execution is deterministic. On every input its error event is empty, hence its error probability is zero and is at most $\varepsilon$. The finite-message characterization of private-coin complexity now gives randomized complexity at most the protocol's cost, and thus at most $n$.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_iff`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_equiv`, `CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
