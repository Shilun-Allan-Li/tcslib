<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-family coefficient union bound

**Claim.** For the specified uniform array of samples, the probability that at least one empirical Fourier coefficient in $\mathcal F$ differs from its true coefficient by at least the accuracy parameter is at most $|\mathcal F|$ times the confidence parameter.

**Proof.** Apply the finite union bound to the bad event for each index $S\in\mathcal F$. For every such index, the single-coefficient estimate (`FABL.measure_finiteFamilyCoefficientBadSetWithParameters_le`) bounds its bad-event probability by the confidence parameter. Summing these bounds over the $|\mathcal F|$ indices gives the result.

**Key facts.** `FABL.measure_finiteFamilyCoefficientBadSetWithParameters_le`.
