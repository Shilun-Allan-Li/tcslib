<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.fourierWeightAtMost_le_three_pow_mul_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Weight Bound

**Claim.** If $f$ takes only the values $0$ and $1$ and has mean $\alpha$, then its Fourier weight on subsets of size at most $k$ is at most $3^k\alpha^{3/2}$.

**Proof.** The low-degree weight estimate at noise parameter $1/3$ bounds $(1/3)^k$ times the weight through degree $k$ by the noise stability at that parameter (`oneThird_pow_mul_fourierWeightAtMost_le_noiseStability`). The small-set expansion bound for a Boolean indicator of mean $\alpha$ bounds that stability by $\alpha^{3/2}$ (`smallSetExpansion_oneThird`). Combining these gives $(1/3)^k\,\mathrm{fourierWeightAtMost}_k(f)\leq\alpha^{3/2}$. Multiplying by the positive factor $3^k$ yields the stated bound, since $3^k(1/3)^k=1$.

**Key facts.** `FABL.oneThird_pow_mul_fourierWeightAtMost_le_noiseStability`, `FABL.smallSetExpansion_oneThird`.
