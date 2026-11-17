<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.pmfLpNorm_two_affine_centered -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Norm of a Centered Affine Function

**Claim.** If X has expectation zero and second moment one under a probability distribution on a finite set Ω, then for all real a,b, the probability norm of order 2 of x ↦ a + bX(x) is √(a²+b²).

**Proof.** First compute the second moment of the affine function. The affine-power expectation formula (FABL.pmfExpectation_affine_pow), applied with exponent 2, expands it into the three terms involving the zeroth, first, and second moments of X. The zeroth moment is 1 by the constant-expectation identity (FABL.pmfExpectation_const), while the assumed first and second moments are 0 and 1. Thus the expectation of (a+bX)² is a²+b². Pointwise, |a+bX|² = (a+bX)², so the same value is the expectation of |a+bX|². By the definition of the order-2 norm, this expectation is raised to the power 1/2, which is its nonnegative square root. Therefore the norm equals √(a²+b²).

**Key facts.** `FABL.pmfExpectation_affine_pow`, `FABL.pmfExpectation_const`.
