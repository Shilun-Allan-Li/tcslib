<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.booleanBlockExpectation_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Block Expectation Formula

**Claim.** The Boolean block expectation of a continuous complex-valued function is the finite weighted sum of its values at the Gaussian torus images, with weights given by the noise kernel and the uniform block weight.

**Proof.** Expand the definition of the Boolean block expectation. Scalar multiplication of a complex-valued function by a scalar is ordinary multiplication of its values, so evaluating the resulting finite sum at $F$ gives the uniform block weight times the double sum of the noise-kernel weights multiplied by $F$ at the corresponding torus images.
