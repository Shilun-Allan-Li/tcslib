<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_cubicScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Learner Work Bound

**Claim.** For the scheduled sample sequence, the low degree polynomial learner's work is at most three times the cube of the stated scale $K$.

**Proof.** Write $D$ for the monomial count, $D_0=(\ell+1)(n+1)^\ell$, $b=b(\delta)$, and $K=2^\ell(D_0+b+2)$. The monomial-count bound gives $D\le D_0$. Since $2^\ell\ge1$, the scale bounds $D_0+b+2$, and therefore bounds $D$, $D+1$, and $D+2$. The scheduled sample count is $2^\ell(D+b)$, which is at most $K$. The general learner-work estimate bounds work by the sum of three terms: sample count times $D+1$, $D$ times sample count times $D+2$, and $D(D+1)$. The first and third are each at most $K^2$, and the middle is at most $K^3$. As $K\ge1$, $K^2\le K^3$, so the total is at most $3K^3$.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`, `FABL.lowDegreeF₂PolynomialLearnerWork_le`.
