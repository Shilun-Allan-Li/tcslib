<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.mFourier_gaussianTorusMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Character of the Gaussian Torus Map

**Claim.** The Fourier character of the Gaussian torus image of a vector is the exponential of the sum of its coordinatewise frequency pairings.

**Proof.** By the definition of the torus Fourier character, it is the product over all pairs $(i,b)$ of the corresponding one-dimensional characters. The character of the class of a real number is its complex exponential, so this product is the exponential of the sum of the corresponding exponents. Regroup the finite sum first by $i$ and then over the two values of $b$. The $b=0$ coordinate contributes $m(i,0)x_i$, while the $b=1$ coordinate contributes $m(i,1)\sqrt{2}x_i$. Combining these terms and factoring out $2\pi x_i$ yields the asserted formula.
