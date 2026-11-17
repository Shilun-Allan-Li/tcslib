<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.abs_fourierCoeff_innerProductModTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient magnitude

**Claim.** For every subset $S$ of the $2n$ coordinates, the absolute value of the Fourier coefficient of the inner product function is $2^{-n}$.

**Proof.** Pair the $2n$ coordinates into $n$ ordered pairs and encode each input by the resulting sequence of Boolean pairs. For each pair, form a local factor consisting of the inner-product sign and the character signs selected by $S$. The product of these local factors is the integrand defining the Fourier coefficient. Summing over all inputs therefore factors into a product of the $n$ local sums. For each pair, whether or not either coordinate belongs to $S$, direct evaluation over the four Boolean pairs shows that the local sum has absolute value $2$. Consequently the absolute Fourier coefficient is the uniform weight $2^{-2n}$ times $2^n$, which simplifies to $2^{-n}$.
