<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.exists_polynomialThreshold_fourierWeightAtMost_lt_two_mul_invPow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small Low-Degree Fourier Weight

**Claim.** For each $k$, there is a Boolean function on the sign cube of dimension $k+1$ that has a polynomial threshold representation of Fourier degree at most $k$ and low-degree squared Fourier weight strictly below $2(1/2)^k$.

**Proof.** Choose the one-point-flipped parity function. It has a polynomial threshold representation of degree at most $k$ (`onePointFlippedParity_isPolynomialThreshold`). Its Fourier weight on sets of size at most $k$ is exactly $(2^{k+1}-1)((1/2)^k)^2$ (`fourierWeightAtMost_onePointFlippedParity`). Since $2^{k+1}-1<2^{k+1}$ and $((1/2)^k)^2>0$, this weight is strictly less than $2^{k+1}((1/2)^k)^2$. The latter equals $2(1/2)^k$, proving the stated bound.

**Key facts.** `FABL.onePointFlippedParity_isPolynomialThreshold`, `FABL.fourierWeightAtMost_onePointFlippedParity`.
