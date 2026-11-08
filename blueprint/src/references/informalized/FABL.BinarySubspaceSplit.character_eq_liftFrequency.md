<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.character_eq_liftFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character from lifted frequency

**Claim.** For every complementary frequency, its character agrees at every point with the sign encoding of the dot product of the lifted frequency and that point.

**Proof.** Fix a point $z$. By definition, the character evaluates the complementary frequency against the second coordinate of the inverse image of $z$ under the splitting isomorphism. The lifted frequency is defined by transporting this same linear functional back to the original cube through the dot-product identification. Evaluating the transported functional at $z$ therefore recovers the original complementary-coordinate evaluation. Applying sign encoding to these equal values proves the pointwise equality, and hence equality of the two functions.
