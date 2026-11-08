<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean :: BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.has_degree_at_most_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for polynomial evaluations

**Claim.** If the coefficients of a multilinear polynomial vanish on sets larger than size $k$, then its evaluation function has Fourier support only on sets of size at most $k$.

**Proof.** Take a set $S$ whose Fourier coefficient for the evaluation function is nonzero. The Fourier coefficient of the evaluation is exactly the polynomial coefficient $p(S)$ (\texttt{MultilinearPolynomial.fourierCoeff_eval}). If $|S|>k$, the degree assumption forces $p(S)=0$, contradicting the chosen nonzero Fourier coefficient. Therefore $|S|\le k$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`.
