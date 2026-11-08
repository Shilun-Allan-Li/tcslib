<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.isPolynomialThreshold_partitionFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Thresholds Under Coordinate Partitioning

**Claim.** If a Boolean function has a polynomial threshold representation of Fourier degree at most $k$, then substituting $z_iw_{\pi(i)}$ for each input coordinate yields another polynomial threshold representation of degree at most $k$.

**Proof.** Choose a polynomial $p$ witnessing the assumed representation and degree bound. Use its partition polynomial as the representing polynomial for the transformed function. The degree bound is preserved by the fact that partitioning does not increase Fourier degree (\texttt{FABL.fourierDegree_partitionPolynomial_le}). For any input $w$, the partition polynomial evaluates to $p((z_iw_{\pi(i)})_i)$ (\texttt{FABL.partitionPolynomial_apply}). The original function at that substituted input is the threshold sign of this value, so the chosen polynomial represents the transformed function.

**Key facts.** `FABL.fourierDegree_partitionPolynomial_le`, `FABL.partitionPolynomial_apply`.
