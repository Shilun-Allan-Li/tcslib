<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComplexity.lean :: CommunicationComplexity.PublicCoin.communicationComplexity_le_of_finiteMessage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Message Protocols Yield Coin-Tape Bounds

**Claim.** If a finite-message public-coin protocol over a finite probability space computes $f$ with error at most $\varepsilon'<\varepsilon$, then the $\varepsilon$-error public-coin communication complexity is at most that protocol’s complexity.

**Proof.** Use the finite-message characterization of a complexity bound (`communicationComplexity_le_iff_finiteMessage`), so it suffices to construct an equally costly protocol over a coin tape that computes within error $\varepsilon$. First express the given error condition as the corresponding satisfaction property (`ApproxComputes_eq_ApproxSatisfies`). Since $\varepsilon-\varepsilon'>0$, apply the finite-space coin-tape conversion: it supplies a coin-tape protocol satisfying the same correctness predicate with error at most $\varepsilon'+(\varepsilon-\varepsilon')=\varepsilon$ (`toCoinTape_approxSatisfies`). The conversion preserves complexity (`toCoinTape_complexity`), so this protocol witnesses the desired bound.

**Key facts.** `CommunicationComplexity.PublicCoin.communicationComplexity_le_iff_finiteMessage`, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies`, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies`, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity`.
