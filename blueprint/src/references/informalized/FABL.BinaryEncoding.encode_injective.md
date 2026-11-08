<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.BinaryEncoding.encode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of binary encoding

**Claim.** If decoding an encoded object recovers that object, then the encoding is injective.

**Proof.** Suppose two objects have the same encoding. Applying the decoder to both sides preserves equality. By the recovery property, the two resulting decoded values are the original objects, each wrapped as a successful decoding. Equality of these successful option values forces the objects to be equal. Thus the encoding is injective.
