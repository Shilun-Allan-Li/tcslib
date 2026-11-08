<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.natCard_polynomialThresholdFunction_le_two_pow_bookBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial threshold book bound

**Claim.** For natural numbers $n$ and $k$, the number of polynomial threshold functions of Fourier degree at most $k$ is at most $2^{n^{k+1}+(2k+1)n^k+1}$.

**Proof.** Split into the cases $n=0$ and $n>0$. When $n=0$, the number of Boolean functions on the empty set of coordinates is $2$, so the number of polynomial threshold functions is at most $2$. The displayed exponent is at least $1$ for every $k$, giving the required bound. When $n>0$, apply the positive-dimension estimate (\texttt{natCard_polynomialThresholdFunction_le_two_pow_bookBound_of_pos}), which gives the stronger bound with exponent $n^{k+1}+(2k+1)n^k$. Increasing an integer exponent cannot decrease a power of $2$; since the target exponent adds $1$, the stated bound follows.

**Key facts.** `FABL.natCard_polynomialThresholdFunction_le_two_pow_bookBound_of_pos`.
