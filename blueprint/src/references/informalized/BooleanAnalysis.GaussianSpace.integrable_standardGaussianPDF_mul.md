<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Integration.lean :: BooleanAnalysis.GaussianSpace.integrable_standardGaussianPDF_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density times an integrable function

**Claim.** If $u$ is integrable under the standard Gaussian measure, then $x\mapsto\varphi(x)u(x)$ is integrable with respect to Lebesgue measure.

**Proof.** The standard Gaussian measure is the measure with density equal to the standard Gaussian density $varphi$ relative to Lebesgue measure. The density-change criterion for integrability identifies integrability under this Gaussian measure with integrability of the function multiplied by its density. Applying that criterion to $u$ proves the claim.
