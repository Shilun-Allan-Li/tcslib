<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.tendsto_limitingMajorityFourierWeightAbove_odd_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Majority Fourier Weight Tail

**Claim.** The tail sum of the limiting majority Fourier weights above the odd cutoff $2q+1$ tends to zero as $q$ tends to infinity.

**Proof.** The weights have total sum $1$ (`limitingMajorityFourierWeight_hasSum_one`), so their partial sums over indices below $m$ tend to $1$ as $m\to\infty$. The cutoff sequence $m=2q+2$ tends to infinity, and therefore the corresponding partial sums also tend to $1$. By the tail identity (`limitingMajorityFourierWeightAbove_eq_one_sub_sum_range`), the tail above $2q+1$ is one minus the partial sum through $2q+2$. Subtracting a sequence converging to $1$ from the constant $1$ shows that these tails tend to zero.

**Key facts.** `FABL.limitingMajorityFourierWeight_hasSum_one`, `FABL.limitingMajorityFourierWeightAbove_eq_one_sub_sum_range`.
