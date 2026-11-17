<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean :: CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-message characterization

**Claim.** The private-coin complexity is at most $n$ exactly when there are coin-tape lengths and a private-coin finite-message protocol on those tapes that meets the error bound on every input and has cost at most $n.

**Proof.** First use the upper-bound characterization to express the inequality by a binary-message protocol. Regard this protocol as a finite-message protocol. Its execution is unchanged (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol\_run}), and its cost is unchanged (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol\_complexity}); therefore its error guarantee and cost bound persist. Conversely, turn a finite-message protocol into a binary-message protocol. The run is preserved (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol\_run}) and so is the cost (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol\_complexity}), hence the error and cost bounds persist in this direction as well. Applying the upper-bound characterization again yields the desired equivalence.

**Key facts.** `CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`.
