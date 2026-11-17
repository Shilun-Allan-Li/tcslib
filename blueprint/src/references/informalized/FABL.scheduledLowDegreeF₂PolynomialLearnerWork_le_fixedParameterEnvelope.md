<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_fixedParameterEnvelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed Parameter Work Envelope

**Claim.** The scheduled learner's work is at most $3\bigl(2^\ell(\ell+b(\delta)+3)\bigr)^3(n+1)^{3\ell}$.

**Proof.** Let $b=b(\delta)$, $P=(n+1)^\ell$, and $K=2^\ell((\ell+1)P+b+2)$ be the cubic scale. Since $P\ge1$, we have $(\ell+1)P+b+2\le(\ell+b+3)P$. Hence $K\le C P$, where $C=2^\ell(\ell+b+3)$. The cubic work bound then gives work at most $3K^3\le3(CP)^3=3C^3(n+1)^{3\ell}$, using $( (n+1)^\ell)^3=(n+1)^{3\ell}$.

**Key facts.** `FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_cubicScale`.
