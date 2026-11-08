<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Protocol Cost Bounds Complexity

**Claim.** If a finite-message deterministic protocol computes $f$ and has cost at most $c\in\mathbb N\cup\{\infty\}$, then $D(f)\le c$.

**Proof.** View the finite-message protocol as an ordinary deterministic protocol. This conversion preserves its execution (\texttt{FiniteMessage.Protocol.toProtocol\_run}) and its cost (\texttt{FiniteMessage.Protocol.toProtocol\_complexity}). The threshold characterization (\texttt{communicationComplexity\_le\_iff}) therefore bounds $D(f)$ by the protocol's natural-number cost. Composing that inequality with the assumed bound of the cost by $c$ gives $D(f)\le c$.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`, `CommunicationComplexity.Deterministic.communicationComplexity_le_iff`.
