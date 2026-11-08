<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.natCard_polynomialThresholdFunction_le_two_pow_bookBound_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Threshold Function Count

**Claim.** For positive $n$, the number of degree-at-most-$k$ polynomial threshold functions on $n$ variables is at most $2^{n^{k+1}+(2k+1)n^k}$.

**Proof.** Each such function is determined by its threshold profile on the low-degree Fourier family, so the profile-count bound gives at most $(2^n+1)^M$ functions, where $M$ is the size of that family (`natCard_polynomialThresholdFunction_le_profileCount`). Since $2^n+1\le 2^{n+1}$, this is at most $2^{(n+1)M}$. The family-size estimate gives $M\le n^k+k n^{k-1}$ (`card_lowDegreeFourierFamily_le_leadingTerm`), hence the exponent is at most $(n+1)(n^k+k n^{k-1})$. Positivity of $n$ implies $n^{k-1}\le n^k$; expanding the exponent and applying this bound yields $(n+1)(n^k+k n^{k-1})\le n^{k+1}+(2k+1)n^k$. Monotonicity of powers of $2$ now gives the claim.

**Key facts.** `FABL.natCard_polynomialThresholdFunction_le_profileCount`, `FABL.two_pow_add_one_le_next_two_pow`, `FABL.card_lowDegreeFourierFamily_le_leadingTerm`.
