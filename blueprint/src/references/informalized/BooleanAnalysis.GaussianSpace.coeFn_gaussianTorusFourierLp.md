<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.coeFn_gaussianTorusFourierLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier representative on Gaussian space

**Claim.** The $L^p(\mu)$ function obtained by pulling back the torus Fourier character indexed by $m$ along the Gaussian torus map agrees $\mu$-almost everywhere with evaluation of that character at the image of each point.

**Proof.** The function in $L^p(\mu)$ is defined by composing the torus Fourier character, viewed as an $L^p$ function for the pushed-forward measure, with the Gaussian torus map. The almost-everywhere representative formula for composition with a measure-preserving map identifies its $L^p$ representative with the character composed with that map. The character has a continuous representative, so its continuous-function representative agrees almost everywhere for the pushed-forward measure; pulling this equality back along the measurable Gaussian torus map gives the claimed equality $\mu$-almost everywhere. The map is measurable because it is continuous (continuous_gaussianTorusMap).

**Key facts.** `BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap`.
