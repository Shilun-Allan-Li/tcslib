<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.continuous_standardGaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the standard Gaussian distribution function

**Claim.** The cumulative distribution function of the standard real Gaussian distribution is continuous.

**Proof.** The cumulative distribution function of any measure is monotone. For a monotone cumulative distribution function, continuity at a point follows when its left limit equals its right limit there; the right-limit identity for Stieltjes functions identifies the right limit with the function value. The standard Gaussian CDF has left limit equal to its value at every real point (`standardGaussianCDF_leftLim`), so these limit identities give continuity at each point, and hence continuity on $\mathbb R$.

**Key facts.** `FABL.standardGaussianCDF_leftLim`.
