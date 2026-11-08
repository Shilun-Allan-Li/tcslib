<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropIdx_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping an Index from a Nested Encoding

**Claim.** Applying the index-dropping operation to the nested encoding of $w,b,b'$ returns the pair encoding of $w,b'$.

**Proof.** The decoding property of pair encoding says that decoding the outer encoding recovers the inner encoding of $w,b$ together with $b'$. Decoding that inner encoding recovers $w,b$. The definition of the operation therefore returns the encoding of $w,b'$, as asserted.

**Key facts.** `Turing.pairDecode_pairEncode`.
