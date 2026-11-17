<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.innerProductModTwoSupportDensity_expectation_gap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support-Density Expectation Gap

**Claim.** For positive $m$, the absolute difference between the support-density expectation of the inner-product indicator and its uniform expectation is $(1+2^{-m})/2$.

**Proof.** The support-density expectation is $1$ (\texttt{innerProductModTwoSupportDensity_expectation}), while the uniform expectation of the indicator is $(1-2^{-m})/2$ (\texttt{expect_booleanRealEmbedding_innerProductModTwoBit}). Their difference is $1-(1-2^{-m})/2=(1+2^{-m})/2$, which is nonnegative. Therefore its absolute value equals that same quantity.

**Key facts.** `FABL.innerProductModTwoSupportDensity_expectation`, `FABL.expect_booleanRealEmbedding_innerProductModTwoBit`.

**Caveat.** The informal statement describes a Fourier-bias result, but the formal statement and proof source establish an expectation-gap identity; this account follows the formal statement and proof.
