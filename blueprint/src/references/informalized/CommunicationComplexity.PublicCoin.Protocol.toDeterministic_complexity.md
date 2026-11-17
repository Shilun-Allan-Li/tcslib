<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.PublicCoin.Protocol.toDeterministic_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Coin Complexity

**Claim.** Fixing the shared randomness of a public-coin protocol preserves its communication complexity.

**Proof.** Use structural induction on the protocol tree. At an output leaf, fixing the coin leaves the same leaf, so both complexities are zero. At an Alice node, fixing the coin composes her Boolean test with the map $x\mapsto(\omega,x)$ and applies the same restriction to each of the two continuation protocols. By induction, each restricted continuation has the same complexity as its original continuation; the node complexity, one plus the maximum of those two branch complexities, is consequently unchanged. At a Bob node the same reasoning applies, using $y\mapsto(\omega,y)$ for his test and the induction hypothesis on both continuations. Thus every node, and in particular the whole protocol, has unchanged complexity.
