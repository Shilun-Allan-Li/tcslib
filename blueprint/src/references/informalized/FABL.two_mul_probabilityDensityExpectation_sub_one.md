<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.two_mul_probabilityDensityExpectation_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine density expectation identity

**Claim.** For a probability density \(\varphi\) and any real-valued function \(h\) on the Boolean cube, \(2\mathbb E_\varphi[h]-1=\mathbb E_\varphi[2h-1]\).

**Proof.** Expand the density expectation as the uniform expectation of a product. By linearity, multiplying that expectation by 2 moves the factor 2 inside, and the density has uniform expectation 1. Thus \(2\mathbb E_\varphi[h]-1=\mathbb E_x[2\varphi(x)h(x)]-\mathbb E_x[\varphi(x)]\). Linearity combines these terms into \(\mathbb E_x[2\varphi(x)h(x)-\varphi(x)]\). Pointwise, this integrand is \(\varphi(x)(2h(x)-1)\), giving the claimed identity.

**Key facts.** `FABL.ProbabilityDensity.expect_eq_one`.
