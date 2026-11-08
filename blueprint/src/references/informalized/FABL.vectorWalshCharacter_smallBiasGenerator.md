<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasGenerator.lean :: FABL.vectorWalshCharacter_smallBiasGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character of the Small-Bias Generator

**Claim.** Evaluating the Walsh character indexed by a binary vector at the small-bias generator gives the same value as evaluating the character indexed by the encoded polynomial value at the encoding of the second field element.

**Proof.** Use the evaluation formula for vector Walsh characters (`vectorWalshCharacter_apply`) on both sides. Both values are the binary sign of a dot product. The dot-product identity for the small-bias generator (`f₂DotProduct_smallBiasGenerator`) says that these two dot products are equal: the sum of the coordinate contributions from the powers of the first field element is the dot product of the encoded polynomial value with the encoding of the second. Applying the same binary sign to equal dot products proves the claim.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_smallBiasGenerator`.
