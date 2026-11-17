<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_iff_finiteMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Message Protocol Characterization

**Claim.** For any function $f$ and natural number $n$, $D(f)\le n$ exactly when there is a finite-message protocol whose execution computes $f$ and whose cost is at most $n$.

**Proof.** First use the threshold characterization (\texttt{communicationComplexity\_le\_iff}) to express $D(f)\le n$ as the existence of an ordinary deterministic protocol computing $f$ with cost at most $n$. In that direction, convert the ordinary protocol to a finite-message protocol using the equivalence of protocol representations (\texttt{FiniteMessage.Protocol.ofProtocol\_equiv}); the conversion preserves both its execution and its cost. Conversely, convert a finite-message protocol to an ordinary one. Its execution is preserved (\texttt{FiniteMessage.Protocol.toProtocol\_run}) and its cost is preserved (\texttt{FiniteMessage.Protocol.toProtocol\_complexity}), so the threshold characterization supplies $D(f)\le n$.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_iff`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_equiv`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`.
