<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianFourierIntegral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of a Gaussian Fourier Integral

**Claim.** For natural number $n$, real number $a$, and $f:\mathbb R^n\to\mathbb C$ integrable with respect to standard Gaussian measure, the function $x\mapsto\int e^{i a\langle t,x\rangle}f(t)\,d\gamma(t)$ is continuous.

**Proof.** The identity `gaussianFourierIntegral_eq` identifies the displayed integral with the vector Fourier integral of $f$, using the continuous bilinear pairing $(t,x)\mapsto a\langle t,x\rangle$. The Fourier integral continuity theorem says that for an integrable function, this vector Fourier integral is continuous when the character is continuous and the pairing is continuous in both variables. Here the character is the real Fourier character, and the pairing has the required continuity, so the desired function is continuous.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianFourierIntegral_eq`.
