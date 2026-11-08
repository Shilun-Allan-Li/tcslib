<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCoefficientFailureBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Confidence Failure-Bit Identity

**Claim.** The number of failure bits at confidence $\delta/(4|\mathcal F|)$ is exactly $\lceil\log_2(\lceil 8|\mathcal F|/\delta\rceil)\rceil$.

**Proof.** By the value formula for the coefficient confidence parameter (\(\texttt{FABL.lowDegreeJuntaCoefficientConfidence_value}\)), its rational value is $(\delta/4)/|\mathcal F|$. Substitute this into the definition of the failure-bit count, which applies the ceiling and then the base-two ceiling logarithm to $2$ divided by the confidence value. Since $|\mathcal F|>0$ by nonemptiness of the family (\(\texttt{FABL.lowDegreeJuntaFourierFamily_nonempty}\)), and $\delta>0$, the denominators are nonzero. Simplifying the rational expression gives $8|\mathcal F|/\delta$, proving the identity.

**Key facts.** `FABL.lowDegreeJuntaCoefficientConfidence_value`, `FABL.lowDegreeJuntaFourierFamily_nonempty`.
