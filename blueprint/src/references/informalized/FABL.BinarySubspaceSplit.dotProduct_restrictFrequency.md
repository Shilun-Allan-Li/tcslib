<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.dotProduct_restrictFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot product of restricted frequency

**Claim.** The dot product of the restricted frequency with any complementary vector equals the dot product of the original frequency with the image of that vector in the original cube.

**Proof.** Under the dot-product identification, the restricted frequency is the functional obtained by evaluating the original frequency on the image of the complementary vector under the splitting map. The restricted frequency is defined by converting that functional back to a vector via the inverse dot-product identification. Evaluating the resulting vector against the complementary vector cancels this inverse conversion, leaving precisely the original frequency evaluated at the image of $(0,a)$.
