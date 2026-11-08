<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.vectorWalshCharacter_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Characters on Concatenated Blocks

**Claim.** The Walsh character indexed by the concatenation of two binary vectors, evaluated at the concatenation of two more, is the product of the corresponding two block characters.

**Proof.** The dot product of two concatenated vectors splits as the sum of the dot products on their respective blocks (`f₂DotProduct_joinF₂CubeBlocks`). By the evaluation formula for a vector Walsh character (`vectorWalshCharacter_apply`), the character on the concatenated vectors is the binary sign of this sum. An additive character sends a sum to the product of its values, so this is the product of the binary signs of the two block dot products. Applying the evaluation formula to each block identifies these factors with the two stated Walsh-character values.

**Key facts.** `FABL.f₂DotProduct_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_apply`.
