<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlockDecode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Snapshot

**Claim.** Decoding the encoded block of any snapshot returns that snapshot.

**Proof.** The encoded block is in the image of the encoding, witnessed by the snapshot itself, so the decoder's existence test succeeds and it selects some snapshot whose encoding is that block. The selected snapshot and the original therefore have equal encodings. Injectivity of snapshot encoding (`Complexity.clBlock_injective`) forces them to be equal, proving that decoding returns the original snapshot.

**Key facts.** `Complexity.clBlock_injective`.
