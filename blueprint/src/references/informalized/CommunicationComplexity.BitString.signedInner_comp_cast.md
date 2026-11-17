<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.signedInner_comp_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reindexing invariance

**Claim.** Precomposing both bit strings with the cast induced by an equality of their index lengths leaves their signed inner product unchanged.

**Proof.** Replace the equality $m=n$ by the resulting identification of the index types. Under this identification, the cast is the identity map on $	ext{Fin }n$, so each coordinate contributes the same signed term before and after precomposition. The sums, and hence the signed inner products, are equal.
