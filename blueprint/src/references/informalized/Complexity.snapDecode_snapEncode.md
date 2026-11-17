<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.snapDecode_snapEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Snapshot

**Claim.** For a finite Turing machine $M$ and any snapshot $s$ of $M$, decoding the encoding of $s$ returns $s$.

**Proof.** The encoding map is injective (`Complexity.snapEncode_injective`). For any injective function, its inverse chosen by `Function.invFun` recovers each element when applied to that element’s image: injectivity ensures that the only preimage of the image of $s$ is $s$. Applying this left-inverse property to the snapshot encoding proves the claim.

**Key facts.** `Complexity.snapEncode_injective`.
