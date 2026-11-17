<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.normalizedBoolSum_lipschitz_comparison -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian comparison for normalized Boolean sums

**Claim.** There is a constant $K>0$ such that for every positive integer $n$, every $c\geq0$, and every $c$-Lipschitz function $\psi$, the uniform Boolean average of $\psi$ applied to the normalized sign sum differs from its standard Gaussian integral by at most $Kc(1/n)^{1/4}$.

**Proof.** Take the positive constant $K$ and comparison estimate supplied by the general theorem for sums of independent random variables with invariance moments (`normalizedSum_lipschitz_comparison`). Realize each coordinate as the sign of the corresponding uniform Boolean coordinate. These coordinate signs are independent under the product uniform measure, by independence of coordinates in a product measure. Each sign has the required invariance moments under the uniform Boolean law (`hasInvarianceMoments_uniformBoolCoordinate`). The general comparison theorem therefore applies to this family of signs, with the given Lipschitz function $\psi$ and constant $c$. Its normalized sum is precisely the Boolean sum in the statement, and its Gaussian comparison term is the standard Gaussian integral. This gives the asserted bound with the same $K$.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedSum_lipschitz_comparison`, `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_uniformBoolCoordinate`.
