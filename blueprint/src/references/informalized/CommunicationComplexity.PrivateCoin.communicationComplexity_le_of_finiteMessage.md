<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean :: CommunicationComplexity.PrivateCoin.communicationComplexity_le_of_finiteMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-probability protocols give complexity bounds

**Claim.** If a finite-message private-coin protocol over finite probability spaces computes $f$ with error at most $\varepsilon'$ and $\varepsilon'<\varepsilon$, then the private-coin complexity at error $\varepsilon$ is at most the protocol's cost.

**Proof.** Rewrite the given computation guarantee as approximate satisfaction of the predicate that the output equals $f(x,y)$ (\texttt{CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes\_eq\_ApproxSatisfies}). The gap $\delta=\varepsilon-\varepsilon'$ is positive. Convert the protocol to one using uniform coin tapes with this slack. The conversion guarantees that approximate satisfaction at error $\varepsilon'$ becomes approximate satisfaction at error $\varepsilon'+\delta$ (\texttt{CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape\_approxSatisfies}); since $\varepsilon'+\delta=\varepsilon$, the resulting coin-tape protocol meets the required error bound. Its communication cost is unchanged (\texttt{CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape\_complexity}). The finite-message characterization then bounds the private-coin complexity by that cost.

**Key facts.** `CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage`, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies`, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies`, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_complexity`.
