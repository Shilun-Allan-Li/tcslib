<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.uniformLpNorm_two_sq_binaryFunctionOnSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment on the Sign Cube

**Claim.** For a real-valued function on the binary cube, viewed on the sign cube through the coordinatewise bijection, the square of its uniform $L^2$ norm on the sign cube equals the uniform average of its square on the binary cube.

**Proof.** By `uniformLpNorm_two_sq_eq_expect_sq`, the squared norm on the sign cube is the uniform average of the square of the transported function. The coordinatewise bijection between the binary cube and the sign cube preserves uniform averages: apply the finite expectation change-of-variables formula along this equivalence (`Fintype.expect_equiv`). Under this change of variables, the transported function evaluated at the corresponding sign point is exactly the original binary-cube function. Its squared average is therefore the stated binary-cube average.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
