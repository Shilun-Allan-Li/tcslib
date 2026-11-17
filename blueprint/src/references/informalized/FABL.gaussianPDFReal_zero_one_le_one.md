<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.gaussianPDFReal_zero_one_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Uniform Density Bound

**Claim.** For every real x, the standard Gaussian density at x is at most 1.

**Proof.** The standard Gaussian density is (2π)^{-1/2} exp(-x²/2). Since π≥2, its normalizing factor is at most 1. Also x²≥0, so exp(-x²/2)≤1. Both factors are nonnegative and at most 1, hence their product is at most 1.
