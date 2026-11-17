<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.concaveOn_gaussianIsoperimetricReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity of the Gaussian Isoperimetric Function

**Claim.** The real-valued Gaussian isoperimetric function is concave on the closed interval $[0,1]$.

**Proof.** Use the criterion that a continuous function on a convex interval is concave when it has a second derivative throughout the interior and that second derivative is nonpositive. The interval $[0,1]$ is convex, and the function is continuous there (`continuousOn_gaussianIsoperimetricReal`). For an interior point $\alpha$, its first derivative is the standard Gaussian upper quantile at $\alpha$ (`hasDerivAt_gaussianIsoperimetricReal`); the quantile is itself differentiable there with derivative $-1/\varphi(\alpha)$, where $\varphi$ is the Gaussian isoperimetric function (`hasDerivAt_standardGaussianUpperQuantileReal`). In identifying the first derivative with this quantile, the real-valued quantile extension agrees with the quantile on the open interval (`standardGaussianUpperQuantileReal_eq`). The resulting second derivative is therefore $-1/\varphi(\alpha)$. Since the function is positive in the interior (`gaussianIsoperimetricReal_pos`), this second derivative is nonpositive. The criterion gives concavity on the whole closed interval.

**Key facts.** `FABL.continuousOn_gaussianIsoperimetricReal`, `FABL.standardGaussianUpperQuantileReal_eq`, `FABL.hasDerivAt_gaussianIsoperimetricReal`, `FABL.hasDerivAt_standardGaussianUpperQuantileReal`, `FABL.gaussianIsoperimetricReal_pos`.
