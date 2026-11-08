<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluenceMain_le_inv_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Square Root Bound

**Claim.** For every natural number $m$, $\sqrt{2/(\pi(2m+1))}\le 1/\sqrt{2m+1}$.

**Proof.** Let $N=2m+1>0$. Both sides are nonnegative, so compare their squares. Their squares are $2/(\pi N)$ and $1/N$, respectively. Since $\pi>3>2$, we have $2/\pi<1$, and dividing by the positive number $N$ gives the required comparison.
