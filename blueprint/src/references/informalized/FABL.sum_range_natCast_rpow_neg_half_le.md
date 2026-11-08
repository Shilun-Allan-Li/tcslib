<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.sum_range_natCast_rpow_neg_half_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Half-Power Sum Bound

**Claim.** For every nonnegative integer $k$, the sum of $j^{-1/2}$ over $0\le j\le k$, with the real-power convention at zero, is at most $2\sqrt{k}$.

**Proof.** Use induction on $k$. At $k=0$, the sum is zero under the real-power convention, so the bound holds. For the step from $k$ to $k+1$, the new summand is $(k+1)^{-1/2}=1/\sqrt{k+1}$. The identity $(\sqrt{k+1}-\sqrt{k})(\sqrt{k+1}+\sqrt{k})=1$ and the inequality $\sqrt{k}\le\sqrt{k+1}$ show that $1/\sqrt{k+1}\le 2(\sqrt{k+1}-\sqrt{k})$. Add this to the induction bound $2\sqrt{k}$. The square-root increments telescope, giving $2\sqrt{k+1}$, as desired.
