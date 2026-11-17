<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.char_S_sq_aux_h -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character Square

**Claim.** For every subset of coordinates and every point of the Boolean hypercube, the square of the Walsh character is $1$.

**Proof.** This is the identity for $chi_S$ supplied by the Boolean-cube character lemma `chiS_sq_eq_one`: the product of the character with itself at any point equals $1$.

**Key facts.** `BooleanAnalysis.chiS_sq_eq_one`.
