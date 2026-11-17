<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.polynomialDerivativeThreshold_isPolynomialThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivatives Lower PTF Degree

**Claim.** If a real-valued function on the sign cube has Fourier degree at most $k$, then its discrete derivative in any coordinate is a polynomial threshold function of degree at most $k-1$.

**Proof.** Use the discrete derivative itself as the threshold polynomial for its threshold function. By definition, the polynomial derivative threshold is obtained by applying the threshold sign to this derivative, so it has the required representation. The discrete derivative degree bound states that differentiating in one coordinate lowers Fourier degree from at most $k$ to at most $k-1$ ($\texttt{fourierDegree\_discreteDerivative\_le\_pred}$). These two facts establish the claimed PTF degree bound.

**Key facts.** `FABL.fourierDegree_discreteDerivative_le_pred`.

**Caveat.** The supplied informal statement describes a larger influence-bound exercise; the Lean declaration proved here is the derivative PTF degree bound stated in the formal statement.
