<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Continuity.lean :: BooleanAnalysis.GaussianSpace.tendsto_eLpNorm_gaussianEndpoint_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of Gaussian rotations in $L^1$

**Claim.** For an integrable function on Gaussian space, the $L^1$ norm of the difference between its values at two Gaussian rotations tends to zero as the rotation parameter $\rho$ tends to $c$.

**Proof.** Write $g_\rho(X,Y)=\cos(\arccos\rho)X+\sin(\arccos\rho)Y$. This map depends continuously on $\rho$ and sends the product Gaussian measure to the standard Gaussian measure, by measure preservation of Gaussian rotations (`measurePreserving_gaussianRotation`). Integrability of $f$ gives an element of $L^1(\gamma)$. Pulling that element back along $g_\rho$ defines a continuous family in $L^1(\gamma\times\gamma)$, since the maps vary continuously and preserve measure. Thus the distance between the family members at $\rho$ and $c$ tends to zero. The $L^1$ distance is exactly the norm in the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`.
