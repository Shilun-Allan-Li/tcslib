<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.exists_majorityFourierConcentrationCutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fourier concentration cutoff for majority

**Claim.** For each $\varepsilon>0$, there are a nonnegative constant $B$ and an odd cutoff $k$ with $k\le (8/\pi^3)\varepsilon^{-2}+B$ such that, for every odd $n$ with $2k^2\le n$, majority's Fourier weight above degree $k$ is at most $\varepsilon$.

**Proof.** The limiting majority tail along odd cutoffs $2q+1$ tends to zero (`tendsto_limitingMajorityFourierWeightAbove_odd_zero`). Choose $q$ so that this limiting tail is less than $\varepsilon$, and set $k=2q+1$. Put $T=(8/\pi^3)\varepsilon^{-2}$ and $B=\max(0,k-T)$; then $B\ge0$ and $k\le T+B$. For any odd $n$ with $2k^2\le n$, the limiting-tail comparison (`limiting_tail_sub_finite_tail_mem_Icc`) says the limiting tail minus the finite majority tail is nonnegative. Therefore the finite tail is no larger than the limiting tail, hence is less than $\varepsilon$ and in particular at most $\varepsilon$. The natural-number cutoff and the real-valued cutoff agree by `fourierWeightAboveReal_natCast`.

**Key facts.** `FABL.tendsto_limitingMajorityFourierWeightAbove_odd_zero`, `FABL.limiting_tail_sub_finite_tail_mem_Icc`, `FABL.fourierWeightAboveReal_natCast`.
