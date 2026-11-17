<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limiting_tail_sub_finite_tail_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Tail Comparison

**Claim.** For odd natural numbers $n$ and $k$ with $2k^2\le n$, the limiting majority Fourier weight above level $k$ exceeds the finite-dimensional weight by an amount between $0$ and $4(2/\pi)^{3/2}k^{-3/2}$.

**Proof.** Since $k$ is positive, the hypothesis implies $2k<n$, and hence every level $j\le k$ lies below $n$ and satisfies $2j<n$. Express both tails as one minus the sum of their weights at levels $0$ through $k$ (the limiting-tail identity `limitingMajorityFourierWeightAbove_eq_one_sub_sum_range` and the finite Boolean Fourier-tail identity `fourierWeightAbove_boolean_eq_one_sub_sum_range`). Their difference is therefore the sum, over these levels, of the finite-level weight minus the limiting weight. Each summand is nonnegative because the limiting weight is at most the finite-level weight (`limitingMajorityFourierWeight_le_finite_level`), proving the lower bound. For the upper bound, the finite-level excess at level $j$ is at most $2j/n$ times the limiting weight (`finite_level_sub_limitingMajorityFourierWeight_le`), since $2j<n$. Summing and applying the weighted limiting-weight estimate gives an upper bound of $\frac{2}{n}\,4(2/\pi)^{3/2}\sqrt{k}$. Finally, $2k^2\le n$ makes this at most $4(2/\pi)^{3/2}/\sqrt{k}=4(2/\pi)^{3/2}k^{-3/2}$.

**Key facts.** `FABL.limitingMajorityFourierWeightAbove_eq_one_sub_sum_range`, `FABL.fourierWeightAbove_boolean_eq_one_sub_sum_range`, `FABL.limitingMajorityFourierWeight_le_finite_level`, `FABL.finite_level_sub_limitingMajorityFourierWeight_le`, `FABL.weighted_limitingMajorityFourierWeight_sum_le`.
