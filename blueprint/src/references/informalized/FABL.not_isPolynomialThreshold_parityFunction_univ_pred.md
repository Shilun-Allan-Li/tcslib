<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ParityThresholdDegree.lean :: FABL.not_isPolynomialThreshold_parityFunction_univ_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Has Full Threshold Degree

**Claim.** For every positive integer $n$, parity on all $n$ coordinates has no polynomial threshold representation whose Fourier degree is at most $n-1$.

**Proof.** Assume such a representation exists, given by a function $p$ whose Fourier degree is at most $n-1$. First, $p$ is not identically zero: choose an input with exactly one coordinate equal to $-1$ (possible since $n>0$). Full parity is $-1$ there, whereas the threshold sign of zero is $1$, contradicting representation if $p=0$.

Let $\mathcal F$ be the family of subsets of coordinates of size at most $n-1$. The Fourier-degree characterization (`fourierDegree_le_iff`) implies that every Fourier coefficient of $p$ indexed by a larger set vanishes. Thus the Fourier support of $p$ lies in $\mathcal F`, using the support criterion (`mem_fourierSupport`). The threshold-representation bound (`one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation`) now gives that the sum over $S\in\mathcal F$ of the absolute values of parity's Fourier coefficients is at least $1$.

But parity's Fourier coefficients are those of the monomial indexed by the full coordinate set (`parityFunction_toReal`). The monomial coefficient formula (`fourierCoeff_monomial`) says this coefficient is zero at every $S\ne [n]$. Every member of $\mathcal F$ differs from $[n]$, since it omits at least one coordinate. Hence the sum in question is zero, contradicting its lower bound of $1$.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.mem_fourierSupport`, `FABL.one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation`, `FABL.parityFunction_toReal`, `FABL.fourierCoeff_monomial`.
