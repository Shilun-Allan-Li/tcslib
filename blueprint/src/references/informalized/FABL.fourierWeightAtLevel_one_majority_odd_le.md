<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.fourierWeightAtLevel_one_majority_odd_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Odd-Majority Weight

**Claim.** For every natural number $m$, the level-one Fourier weight of majority on $2m+1$ coordinates is at most $2/\pi+2/(\pi(2m+1))$.

**Proof.** The exact odd-majority formula expresses this weight as $N$ times the square of the odd-majority influence, where $N=2m+1$ (`fourierWeightAtLevel_one_majority_odd`). The influence-square bound gives at most $2(N+1)/(\pi N^2)$ (`oddMajorityInfluence_sq_le`). Since $N>0$, multiplying that estimate by $N$ and simplifying gives $2/\pi+2/(\pi N)$, as required.

**Key facts.** `FABL.fourierWeightAtLevel_one_majority_odd`, `FABL.oddMajorityInfluence_sq_le`.
