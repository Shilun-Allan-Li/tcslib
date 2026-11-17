<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.shifted_limitingMajorityFourierWeight_tsum_eq_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Indexed Tail Sum Identity

**Claim.** For odd $k$, the tail sum of limiting majority Fourier weights starting at $k+1$ equals the sum of weights at indices $k+2(r+1)$ for $r\ge0$.

**Proof.** Write $A(j)$ for the limiting majority Fourier weight and set $f(r)=A(k+1+r)$. The full weight sequence is summable, since its terms have sum one (\texttt{limitingMajorityFourierWeight\_hasSum\_one}); hence both subsequences $f(2r)$ and $f(2r+1)$ are summable. Splitting a summable series into its even and odd positions expresses $\sum_r f(r)$ as the sum of those two subsequence sums. Since $k$ is odd, every index $k+1+2r$ is even. The weight at every even index is zero by the parity formula for the limiting majority Fourier weight (\texttt{limitingMajorityFourierWeight\_eq}), so the even-position sum vanishes. The remaining indices satisfy $k+1+(2r+1)=k+2(r+1)$, giving the asserted identity.

**Key facts.** `FABL.limitingMajorityFourierWeight_hasSum_one`, `FABL.limitingMajorityFourierWeight_eq`.
