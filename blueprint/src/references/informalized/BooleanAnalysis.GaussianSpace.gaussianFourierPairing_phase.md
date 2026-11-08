<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.gaussianFourierPairing_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase of the Gaussian Fourier Pairing

**Claim.** For real $a$ and vectors $x,y\in\mathbb R^n$, the Gaussian Fourier pairing satisfies $-2\pi$ times the pairing equal to $a\sum_jx_jy_j$.

**Proof.** Expand the pairing as the scalar $-a/(2\pi)$ times the sum of the coordinate projection pairings. Each projection pairing evaluates to $x_jy_j$. Multiplying by $-2\pi$ cancels the defining scalar, leaving $a$ times the coordinate sum; distributing the scalar through the finite sum and simplifying signs gives the identity.
