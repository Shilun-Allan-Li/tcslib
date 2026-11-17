<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.fourier_coeff_convolution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Convolution

**Claim.** The Fourier coefficient of the convolution of $f$ and $g$ at $s$ is the product of their Fourier coefficients at $s$.

**Proof.** Expand the definitions of convolution, Fourier coefficient, inner product, and expectation. The left side becomes a normalized finite double sum over the convolution variable and the averaging variable. Swap the order of these finite sums and regroup the factors. For each fixed convolution variable, translate the averaging variable by that fixed vector; translation is a bijection of the finite group, so this reindexing does not change the sum. The character evaluated at the resulting sum of vectors factors as the product of its values on the two vectors, by the character addition law (`char_s_add`). The regrouped expression is exactly the product of the two normalized sums defining the Fourier coefficients of $f$ and $g$.

**Key facts.** `ZkFourier.char_s_add`.
