<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.BinaryEncoding.encode_mem_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded strings are decodable

**Claim.** Every encoded string belongs to the language of strings on which the decoder is defined.

**Proof.** For any object, decoding its encoding returns that object as a successful decoding. In particular, the decoder’s result is defined, so the encoded string belongs to the language.
