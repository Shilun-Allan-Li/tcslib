<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.fourier_coeff_convolution_aux_h_fubini -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interchange of Convolution Sums

**Claim.** The sum over $x$ of the inner convolution sum, weighted by $\chi_S(x)$, equals the iterated sum in which $y$ is summed outside and $x$ inside.

**Proof.** Both sums are finite sums over the same pairs $(x,y)$. Distribute the factor $\chi_S(x)$ into the inner sum and use associativity of multiplication to write each summand as $f(y)g(x\oplus y)\chi_S(x)$. Interchanging the order of the two finite sums then gives the claimed expression.
