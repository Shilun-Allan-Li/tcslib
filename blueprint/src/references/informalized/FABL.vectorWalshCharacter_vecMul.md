<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.vectorWalshCharacter_vecMul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Characters Under Matrix Multiplication

**Claim.** Evaluating the Walsh character indexed by a vector at the row-vector product with a matrix equals evaluating the character indexed by the matrix-vector product at the original vector.

**Proof.** By the evaluation formula for vector Walsh characters (`vectorWalshCharacter_apply`), each side is the binary sign of the corresponding dot product. The dot-product identity for matrix multiplication (`f₂DotProduct_vecMul`) equates those dot products. Their binary signs, and therefore the two character values, are equal.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_vecMul`.
