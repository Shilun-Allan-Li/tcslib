<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.map_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output mapping and randomized execution

**Claim.** Executing the protocol obtained by applying $g\colon\alpha\to\beta$ to the output gives $g$ applied to the original protocol’s randomized output.

**Proof.** Randomized execution evaluates the deterministic protocol on $(\omega,x)$ and $(\omega,y)$. The deterministic map execution law says that running a protocol whose output is mapped by $g$ yields $g$ of the original run (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map\_run}). Applying it to these paired inputs proves the equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`.
