<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorWalshCharacter_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Vector Walsh Characters

**Claim.** Distinct vectors in the binary cube determine distinct Walsh characters.

**Proof.** Suppose two vectors give the same Walsh character. Each vector is identified with the finite set of coordinates on which it is nonzero; this identification is injective, since a binary vector is recovered coordinate by coordinate from its support. Equality of the characters therefore gives equality of the two support-indexed characters. The injectivity of the support-indexed Walsh-character map (`binaryWalshCharacter_injective`) implies that the supports are equal, and hence the original vectors are equal.

**Key facts.** `FABL.binaryWalshCharacter_injective`.
