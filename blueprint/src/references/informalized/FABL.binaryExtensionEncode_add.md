<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/FiniteFields.lean :: FABL.binaryExtensionEncode_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the Binary Extension Encoding

**Claim.** For the chosen linear encoding of the binary extension field by its coordinates, encoding a sum gives the sum of the encodings.

**Proof.** The encoding is a linear map over $\mathbb F_2$. Every linear map preserves addition, so applying it to $a+b$ yields the sum of its values on $a$ and $b.

**Caveat.** The supplied informal statement also mentions construction time and the number of field elements; the formal theorem proved here asserts only additivity of the encoding.
