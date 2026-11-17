<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.abs_fourierWeightAtLevel_majority_div_levelMain_sub_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Fourier level estimate

**Claim.** For odd $n$ and odd $k$ satisfying $2k^2\le n$, the ratio of the level-$k$ Fourier weight of majority to its main asymptotic term differs from $1$ by at most $3/k$.

**Proof.** Because $k$ is positive, the main term is positive. The numerical hypothesis and oddness give the stricter inequality $2k<n$ (\texttt{FABL.two\_mul\_lt\_of\_odd\_of\_two\_mul\_sq\_le}). First, the main term is at most the limiting majority Fourier weight, which in turn is at most the level-$k$ weight at dimension $n$ (\texttt{FABL.majorityFourierLevelMain\_le\_limitingMajorityFourierWeight}; \texttt{FABL.limitingMajorityFourierWeight\_le\_fourierWeightAtLevel\_majority}). This gives a ratio of at least $1$.

For the upper bound, the finite-dimensional level weight is at most $(1+2k/n)$ times the limiting weight (\texttt{FABL.fourierWeightAtLevel\_majority\_le\_limitingMajorityFourierWeight}). The hypothesis $2k^2\le n$ implies $2k/n\le1/k$. The limiting weight is at most the main term multiplied by $(1+1/k)$ (\texttt{FABL.limitingMajorityFourierWeight\_le\_levelMain\_mul}); hence the level weight is bounded by the main term times $(1+1/k)^2$. Since $k\ge1$, we have $(1/k)^2\le1/k$, so $(1+1/k)^2\le1+3/k$. Dividing by the positive main term gives the upper ratio bound $1+3/k$. Together with the lower bound $1$, this yields the asserted absolute deviation estimate.

**Key facts.** `FABL.two_mul_lt_of_odd_of_two_mul_sq_le`, `FABL.majorityFourierLevelMain_le_limitingMajorityFourierWeight`, `FABL.limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority`, `FABL.fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight`, `FABL.limitingMajorityFourierWeight_le_levelMain_mul`.
