<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Inputs.lean :: BooleanAnalysis.GaussianSpace.HasInvarianceMoments.identDistrib -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance moments under equal distributions

**Claim.** If $X$ satisfies the invariance moment conditions and $X$ and $Y$ have the same distribution under the given measures, then $Y$ satisfies those conditions under its measure.

**Proof.** Equality in distribution transfers integrability of the fourth moment from $X$ to $Y$, and the target measure is already a probability measure. It also transfers each of the first, second, and third moments: applying the distributional integral identity to the identity function and to the second and third powers shows that these moments for $Y$ equal those for $X$. For the fourth-moment bound, apply the same identity to the fourth and second powers. The resulting inequality for $Y$ is exactly the fourth-moment bound for $X$, with the second moment of $Y$ replaced by its equal value for $X>.
