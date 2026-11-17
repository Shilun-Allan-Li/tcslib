<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaRestrictedSampleCount_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted sample count bound

**Claim.** The restricted sample count at the specified dyadic node failure parameter is at most the stated linear-confidence resource bound.

**Proof.** Split the restricted sample count into its Fourier batch contribution and polynomial sample contribution. The Fourier batch bound controls the first by its coefficient times $(n+1)^{q+1}(b+1)$, while the polynomial bound controls the second by its coefficient times $(n+1)^\ell(b+1)$. The runtime exponent ledger gives $q\le q+3$ and $3\ell\le q+3$, hence in particular $\ell\le q+3$. Since $n+1$ is positive, increasing either exponent to $q+3$ can only increase its power. Add the two bounds and factor out the common power and confidence factor; the sum of the two coefficients is the restricted-sample linear coefficient.

**Key facts.** `FABL.lowDegreeJuntaFourierBatchSize_le_linearConfidence`, `FABL.lowDegreeJuntaPolynomialSampleCount_le_linearConfidence`, `FABL.lowDegreeJuntaRuntimeExponentLedger`.
