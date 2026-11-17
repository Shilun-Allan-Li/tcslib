<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_power_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power bounds for the odd-level tail

**Claim.** For odd $k$, the tail $T(k)$ satisfies $(2/\pi)^{3/2}(k+2)^{-1/2}\leq T(k)\leq(2/\pi)^{3/2}\bigl(k^{-1/2}+(1/3)k^{-3/2}\bigr)$.

**Proof.** Write $k=2q+1$ and index the odd levels above $k$ by $2(r+q+1)+1$, for $r\geq0$. The tail is the sum of the weights at these levels. At each such level, the leading approximation to the weight is $c(2(r+q+1)+1)^{-3/2}$, where $c=(2/\pi)^{3/2}$; the weight is at least this main term and at most this main term plus $c(2(r+q+1)+1)^{-5/2}$. These comparisons are supplied by the lower main-term bound (FABL.majorityFourierLevelMain_le_limitingMajorityFourierWeight) and the upper level estimate (FABL.limitingMajorityFourierWeight_le_levelMain_mul). The weight series is summable because all weights have total sum one (FABL.limitingMajorityFourierWeight_hasSum_one). The main and error series are summable as well: the error terms are bounded by the main terms, since each level is at least one, and the main terms are bounded by the summable weight terms.

For exponents $-3/2$ and $-5/2$, comparison of the decreasing power function with its integral bounds the corresponding sums from below by the integral starting at $q+1$ and from above by the integral starting at $q$ (FABL.two_mul_add_one_rpow_tail_bounds). Integrating $(2x+1)^s$ over $(a,\infty)$ gives $-(2a+1)^{s+1}/(2(s+1))$ (FABL.integral_Ioi_two_mul_add_one_rpow). Thus the lower comparison, using the $-3/2$ main series, gives $c(2q+3)^{-1/2}=c(k+2)^{-1/2}$. For the upper comparison, integrate both the $-3/2$ main series and the $-5/2$ error series from $q$: their values are respectively $(2q+1)^{-1/2}$ and $(1/3)(2q+1)^{-3/2}$. Adding them and substituting $k=2q+1$ gives the asserted upper bound.

**Key facts.** `FABL.majorityFourierLevelMain_le_limitingMajorityFourierWeight`, `FABL.limitingMajorityFourierWeight_le_levelMain_mul`, `FABL.limitingMajorityFourierWeight_hasSum_one`, `FABL.two_mul_add_one_rpow_tail_bounds`, `FABL.integral_Ioi_two_mul_add_one_rpow`, `FABL.limitingMajorityFourierWeightAbove_eq_tsum_odd`.
