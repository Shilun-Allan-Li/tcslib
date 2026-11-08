<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_eq_one_sub_sum_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight tail from total mass

**Claim.** For every $k$, the limiting majority Fourier weight above $k$ equals $1-\sum_{j=0}^{k} w_j$, where $w_j$ is the limiting majority Fourier weight at level $j$.

**Proof.** The weights have total sum $1$ (`FABL.limitingMajorityFourierWeight_hasSum_one`). Split this convergent sum into the finite initial segment with indices in $\{0,\ldots,k\}$ and its complementary tail. The complement consists exactly of indices $j>k$, so its sum is the weight above $k$. Therefore the initial sum plus that tail is $1$, and rearranging yields the formula.

**Key facts.** `FABL.limitingMajorityFourierWeight_hasSum_one`.
