<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.limitingMajorityFourierWeight_pos_of_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity at odd levels

**Claim.** For every odd natural number $k$, the limiting majority Fourier weight at level $k$ is positive.

**Proof.** Write $k=2j+1$. The explicit formula for the limiting weight at this odd level is $4/(\pi k2^k)$ times the central binomial coefficient $\binom{k-1}{(k-1)/2}$ (FABL.limitingMajorityFourierWeight_eq). Here $k-1=2j$ and $(k-1)/2=j$, so the binomial coefficient is $\binom{2j}{j}$, which is positive. The remaining factors are also positive, proving the claim.

**Key facts.** `FABL.limitingMajorityFourierWeight_eq`.
