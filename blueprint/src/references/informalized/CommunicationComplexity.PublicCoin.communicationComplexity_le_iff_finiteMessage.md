<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComplexity.lean :: CommunicationComplexity.PublicCoin.communicationComplexity_le_iff_finiteMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Message Characterization

**Claim.** The public-coin communication complexity is at most $m$ exactly when a finite-message public-coin protocol on some coin tape both $\varepsilon$-computes $f$ and has complexity at most $m$.

**Proof.** First use the characterization of complexity bounds by an approximating binary protocol (`communicationComplexity_le_iff`). In the forward direction, convert that protocol to a finite-message protocol using `ofProtocol`. This preserves its run on every input (`ofProtocol_run`), so the error probability is unchanged, and preserves its complexity (`ofProtocol_complexity`). In the reverse direction, convert a finite-message protocol to a binary protocol using `toProtocol`. Its run agrees with the original (`toProtocol_run`), hence its approximation guarantee is preserved, and its complexity is unchanged (`toProtocol_complexity`). The two conversions give the required witnesses in each direction.

**Key facts.** `CommunicationComplexity.PublicCoin.communicationComplexity_le_iff`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`.
