<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_coeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate derivative coefficients

**Claim.** For each subset $S$, the coefficient of the polynomial formed from the Fourier coefficients of the Boolean-cube derivative is zero when $i\in S$, and equals $F(S\cup\{i\})$ when $i\notin S$.

**Proof.** By definition, the coefficient at $S$ is the Fourier coefficient at $S$ of the Boolean-cube derivative of the Walsh evaluation of $F$. The Fourier coefficient formula for a Boolean-cube derivative says this is zero if $i\in S$, and otherwise is the Fourier coefficient of the original function at $S\cup\{i\}$. The Walsh expansion of $F$ has Fourier coefficient at each set equal to its original coefficient there, so the latter quantity is $F(S\cup\{i\})$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.fourierCoeff_derivative`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`.
