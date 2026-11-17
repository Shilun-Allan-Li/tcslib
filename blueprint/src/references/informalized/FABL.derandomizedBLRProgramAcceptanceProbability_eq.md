<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.derandomizedBLRProgramAcceptanceProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability identity

**Claim.** For every target Boolean function and seed map, the program’s acceptance probability equals the derandomized BLR acceptance probability of the encoded target under the density induced by the seed map.

**Proof.** First write the uniform expectation over pairs of input bits and seed bits as an iterated expectation over those two finite spaces. At each pair, the program result is exactly the BLR acceptance test for the encoded target at the input represented by the input bits and the cube point returned by the seed map. Replacing the input-bit expectation by an expectation over the binary cube is valid because the bit-to-cube map is an equivalence. Finally, the density induced by the seed map converts expectation over seed bits into the density-weighted expectation on the cube: this is the uniform-pushforward expectation identity (`ProbabilityDensity.expectation_uniformPushforward`). The resulting iterated expectation is precisely the stated derandomized BLR acceptance probability.

**Key facts.** `FABL.ProbabilityDensity.expectation_uniformPushforward`.
