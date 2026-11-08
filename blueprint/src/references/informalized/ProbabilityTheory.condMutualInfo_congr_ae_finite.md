<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.condMutualInfo_congr_ae_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-space almost-sure invariance

**Claim.** On the stated finite sample and value spaces, if $X=X'$, $Y=Y'$, and $Z=Z'$ almost everywhere, then $I[X:Y\mid Z;\mu]=I[X':Y'\mid Z';\mu]$.

**Proof.** Because the value spaces are finite, each random variable has finite range. The finite sample space carries the discrete measurable structure, so all the variables are measurable. The general almost-sure invariance theorem for conditional mutual information (`ProbabilityTheory.condMutualInfo_congr_ae`) now applies directly to the three almost-everywhere equalities and gives the claimed equality.

**Key facts.** `ProbabilityTheory.condMutualInfo_congr_ae`.
