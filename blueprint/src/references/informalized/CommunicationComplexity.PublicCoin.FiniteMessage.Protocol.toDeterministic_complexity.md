<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity preserved by fixing randomness

**Claim.** Fixing any shared-randomness outcome in a public-coin finite-message protocol yields a deterministic finite-message protocol with the same communication complexity.

**Proof.** Substituting the fixed outcome into both parties' effective inputs is a pullback along the maps $x\mapsto(\omega,x)$ and $y\mapsto(\omega,y)$. This changes the inputs to the message-selection functions, but leaves the message alphabets and continuation branches intact. The recursive definition of complexity depends on those alphabets and branches, so the complexity is unchanged.
