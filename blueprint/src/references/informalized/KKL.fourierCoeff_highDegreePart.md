<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.fourierCoeff_highDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of the high-degree part

**Claim.** The Fourier–Walsh coefficient of the part of $f$ supported on sets of size greater than $d$, at frequency $T$, is $\widehat f(T)$ when $|T|>d$ and $0$ otherwise.

**Proof.** The high-degree part is the multilinear polynomial whose coefficient at each set $S$ is $\widehat f(S)$ when $|S|>d$ and zero otherwise. By the Fourier coefficient formula for evaluating a multilinear polynomial (BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval), the Fourier coefficient of its evaluation at frequency $T$ is exactly its polynomial coefficient at $T$. Substituting the specified coefficient gives the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`.
