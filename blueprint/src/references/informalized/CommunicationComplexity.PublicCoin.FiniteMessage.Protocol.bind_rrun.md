<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.bind_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bind and randomized execution

**Claim.** For any public-coin protocols $p$ and continuation family $q$, executing their sequential composition with fixed inputs and shared randomness gives the same output as executing $p$ first and then the continuation selected by its output.

**Proof.** Unfold randomized execution: both sides run the corresponding deterministic protocols on the paired inputs $(\omega,x)$ and $(\omega,y)$. The deterministic bind execution law says that running a bound protocol on fixed inputs equals running the continuation selected by the first protocol’s output on those same inputs (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind\_run}). Applying that law gives the claimed equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`.
