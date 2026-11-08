<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.hasDerivAt_gaussianIsoperimetricReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the extended Gaussian profile

**Claim.** At every $\alpha\in(0,1)$, the real-valued Gaussian isoperimetric profile obtained by extension is differentiable, with derivative the standard Gaussian upper quantile at $\alpha$.

**Proof.** The interior profile has the stated derivative at $\alpha$ (`FABL.hasDerivAt_gaussianIsoperimetricInterior`). Because $(0,1)$ is open, there is a neighborhood of $\alpha$ contained in it. Throughout that neighborhood, the extension agrees with the interior profile: the interior profile is continuous on $(0,1)$ (`FABL.continuousOn_gaussianIsoperimetricInterior`), so the extension agrees there by the extension property. Functions that agree on a neighborhood have the same derivative at its center, giving the claimed derivative for the extended profile.

**Key facts.** `FABL.hasDerivAt_gaussianIsoperimetricInterior`, `FABL.continuousOn_gaussianIsoperimetricInterior`.
