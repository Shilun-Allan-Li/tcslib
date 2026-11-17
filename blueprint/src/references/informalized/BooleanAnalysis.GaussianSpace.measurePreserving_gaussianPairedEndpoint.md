<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianPairedEndpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent paired Gaussian mixtures

**Claim.** The two vectors formed by the respective cosine-sine mixtures have the product law of two standard Gaussian vectors.

**Proof.** Let $\mu$ be the product standard Gaussian law on $\mathbb R^n$. The planar rotation result (`measurePreserving_gaussianRotation`) says that rotating a pair of independent vectors with law $\mu$ preserves their product law. Projecting the rotated pair onto its first component therefore shows that $\bigl(x,y\bigr)\mapsto (\cos u)x+(\sin u)y$ sends $\mu\otimes\mu$ to $\mu$. Apply this fact separately to the first and second pairs of inputs: the product of these two measure-preserving maps sends the product law of the two pairs to $\mu\otimes\mu$. The middle-coordinate transpose result (`measurePreserving_middleTranspose`) first rearranges the four independent inputs so that each pair consists of the inputs used in one mixture. Composing the rearrangement with the two mixture maps proves the assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`, `BooleanAnalysis.GaussianSpace.measurePreserving_middleTranspose`.
