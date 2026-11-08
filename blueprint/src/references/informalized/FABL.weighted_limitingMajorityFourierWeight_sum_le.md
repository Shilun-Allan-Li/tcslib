<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.weighted_limitingMajorityFourierWeight_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Fourier-Weight Sum Bound

**Claim.** For every natural number $k$, the sum of $j$ times the limiting majority Fourier weight over $0\leq j\leq k$ is at most $4(2/\pi)^{3/2}\sqrt{k}$.

**Proof.** Bound each summand according to the parity of $j$. For even $j$, the limiting majority Fourier weight is zero (\texttt{limitingMajorityFourierWeight\_eq}), so the summand is zero. For odd $j$, the level estimate (\texttt{limitingMajorityFourierWeight\_le\_levelMain\_mul}) bounds the weight by the main level term times $1+1/j$. Rewriting the power of $j$ using (\texttt{odd\_rpow\_neg\_three\_halves\_eq\_neg\_half\_div}), and using $j\geq1$ to bound $1+1/j\leq2$, gives $j$ times the weight at most $2(2/\pi)^{3/2}j^{-1/2}$. Summing these pointwise bounds reduces the claim to the inverse-square-root sum estimate (\texttt{sum\_range\_natCast\_rpow\_neg\_half\_le}), which bounds that sum by $2\sqrt{k}$. Multiplication by the nonnegative constant $2(2/\pi)^{3/2}$ gives the asserted bound.

**Key facts.** `FABL.limitingMajorityFourierWeight_eq`, `FABL.limitingMajorityFourierWeight_le_levelMain_mul`, `FABL.odd_rpow_neg_three_halves_eq_neg_half_div`, `FABL.sum_range_natCast_rpow_neg_half_le`.
