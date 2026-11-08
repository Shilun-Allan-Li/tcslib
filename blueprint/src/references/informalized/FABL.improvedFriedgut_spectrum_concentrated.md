<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_spectrum_concentrated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier concentration on a large family

**Claim.** The Fourier weight outside the family consisting of sets either contained in the threshold-influential coordinates or larger than $k$ is at most $\epsilon$.

**Proof.** By the identity for weight outside the improved Friedgut family (`fourierWeightOutside_improvedFriedgutFamily`), this outside weight equals the low-degree Fourier mass outside the threshold-influential coordinates. The threshold mass estimate (`lowDegreeOutsideInfluentialMass_improvedThreshold_le`) bounds that quantity by $\epsilon$ under the positivity assumptions. Substitution gives the claimed concentration bound.

**Key facts.** `FABL.fourierWeightOutside_improvedFriedgutFamily`, `FABL.lowDegreeOutsideInfluentialMass_improvedThreshold_le`.
