<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.IsBiased.convolutionPower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias Under Convolution Powers

**Claim.** If \(\phi\) is \(\varepsilon\)-biased, then its \(d\)-fold convolution power is \(\varepsilon^d\)-biased for every natural number \(d\).

**Proof.** Take any nonzero frequency \(\gamma\). The Fourier coefficient of the convolution power at \(\gamma\) is the \(d\)-th power of the Fourier coefficient of \(\phi\) there (\texttt{FABL.ProbabilityDensity.vectorFourierCoeff\_convolutionPower}). Taking absolute values turns this into the \(d\)-th power of the original absolute value. The bias assumption bounds that value by \(\varepsilon\); since both sides are nonnegative, raising the inequality to the natural power \(d\) gives the required bound \(\varepsilon^d\).

**Key facts.** `FABL.ProbabilityDensity.vectorFourierCoeff_convolutionPower`.
