<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.char_S_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character Square

**Claim.** For every subset of coordinates and every point of the Boolean hypercube, the Walsh character takes a value whose square is $1$.

**Proof.** The auxiliary identity `char_S_sq_aux_h` establishes that the square of the Walsh character at the given point is $1$. Rewriting the square as the product of the character with itself gives the stated identity.

**Key facts.** `BoolFourier.char_S_sq_aux_h`.
