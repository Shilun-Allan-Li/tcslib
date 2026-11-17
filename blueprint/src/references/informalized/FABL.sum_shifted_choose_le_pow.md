<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.sum_shifted_choose_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Binomial Sum Bound

**Claim.** For every nonnegative integer $m$, $\sum_{j=0}^{m}\binom{m+2}{j+2}\le 2^{m+2}$.

**Proof.** The binomial theorem gives $\sum_{j=0}^{m+2}\binom{m+2}{j}=2^{m+2}$. The sum in question consists of the terms with indices $2$ through $m+2$, so it is at most the full sum because the omitted terms, at indices $0$ and $1$, are nonnegative.
