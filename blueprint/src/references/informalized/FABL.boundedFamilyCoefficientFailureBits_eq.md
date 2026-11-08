<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.boundedFamilyCoefficientFailureBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Family Failure Bit Count

**Claim.** For positive integer $M$, the failure-bit count at confidence parameter $1/(20M)$ equals $\operatorname{clog}_2(40M)$.

**Proof.** By definition, the failure-bit count is the base-two ceiling logarithm of the ceiling of twice the reciprocal of the confidence parameter. The specified confidence parameter is $1/(20M)$, so twice its reciprocal is $40M$. This is already a natural number, and the ceiling of a natural number viewed as a rational is that same number. Thus the count is $\operatorname{clog}_2(40M)$.
