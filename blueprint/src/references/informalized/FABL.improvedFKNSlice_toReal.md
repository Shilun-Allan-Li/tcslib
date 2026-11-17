<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.improvedFKNSlice_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-valued first-coordinate slice

**Claim.** The real-valued version of the restriction of a sign-valued function to inputs with first coordinate $b$ is the first-coordinate slice of its real-valued version.

**Proof.** At any input in the remaining coordinates, both functions evaluate the original sign-valued function on the tuple formed by placing $b$ in the first coordinate, and then take its real value. They agree pointwise, so the functions are equal.
