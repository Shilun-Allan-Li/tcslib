<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaPolynomialWork_le_fixedParameterEnvelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Parameter Polynomial Work Envelope

**Claim.** The work of the polynomial learner on the extracted polynomial samples is bounded by the fixed-parameter envelope stated in the theorem.

**Proof.** Apply the scheduled polynomial learner work bound to the restricted dimension $r$ and degree $\ell$, using the quartered failure parameter and the polynomial samples. This bounds the work by $3\bigl(2^\ell(\ell+\text{failure bits}+3)\bigr)^3(r+1)^{3\ell}$. The restriction dimension satisfies $r\le n$ (`juntaRestrictionDimension_le`), hence $(r+1)^{3\ell}\le(n+1)^{3\ell}$. Multiplying this inequality by the nonnegative prefactor yields the claimed envelope.

**Key facts.** `FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_fixedParameterEnvelope`, `FABL.juntaRestrictionDimension_le`.
