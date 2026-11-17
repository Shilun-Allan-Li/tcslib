<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.boundedFamilySampleCount_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Family Sample Count

**Claim.** For a positive rational learning accuracy $\varepsilon$ and positive integer $M$, the bounded-family sample count is at most $640M^3/\varepsilon^2$.

**Proof.** Apply the Fourier estimator sample-count bound to the bounded-family accuracy and confidence parameters. By the failure-bit identity, the resulting count is at most $4\operatorname{clog}_2(40M)/(\varepsilon/(2M))^2$, which simplifies to $16M^2\operatorname{clog}_2(40M)/\varepsilon^2$. The ceiling logarithm is at most its argument: indeed, $40M\le 2^{40M}$, so the defining least exponent is at most $40M$. Substituting this bound gives $640M^3/\varepsilon^2$.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`, `FABL.boundedFamilyCoefficientFailureBits_eq`, `FABL.nat_self_le_two_pow`.
