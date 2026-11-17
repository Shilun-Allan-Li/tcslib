<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.char_S_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Walsh character

**Claim.** For every $n$, the Walsh character associated with the empty subset is the constant function equal to $1$ on the Boolean hypercube.

**Proof.** The empty-set Walsh character is the constant-one function, by the empty-product identity for the character construction (`BooleanAnalysis.chiS_empty`). Since the Walsh character notation abbreviates that construction, the same identity gives the claim.

**Key facts.** `BooleanAnalysis.chiS_empty`.
