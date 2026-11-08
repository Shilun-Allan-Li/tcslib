<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of Coin-Tape Conversion

**Claim.** For every positive tolerance, converting a finite-randomness protocol to a coin-tape protocol preserves its communication complexity.

**Proof.** The conversion precomposes each party’s input with a map that changes only the randomness coordinate and leaves the ordinary input unchanged. Such precomposition preserves the protocol’s message branches and their message alphabets, so the recursive complexity calculation is unchanged at every node. Unfolding the conversion and simplifying these unchanged complexity expressions yields equality of the two complexities.
