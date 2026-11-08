<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.uniformPMF_finZeroArrowBool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform law on the empty function space

**Claim.** The uniform distribution on functions from the empty set to $\{\mathrm{false},\mathrm{true}\}$ is concentrated on the unique empty function.

**Proof.** There is exactly one function with empty domain: every function on that domain agrees with the empty function, since there are no inputs at which they could differ. The function space is therefore a singleton, and its uniform distribution assigns probability one to that sole element. This is the point mass at the empty function.
