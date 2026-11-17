<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.expect_sup_le_clog_add_two_of_twoPow_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Maximum Depth Bound

**Claim.** If each of the $m$ depth functions has expected $2^{	ext{depth}}$ at most $2$ under the same random restriction, then the expected maximum depth is at most $\lceil\log_2(m+1)\rceil+2$.

**Proof.** Let $q=\lceil\log_2(m+1)\rceil$, so $m+1\le 2^q$. For each restriction, write $D$ for the maximum depth. The pointwise estimate $D\le q+2^D/2^q$ follows from the elementary inequality that a natural number $d$ is at most $q+2^d/2^q$ (`natCast_le_add_pow_div_pow`). Also, $2^D\le 1+\sum_i 2^{\mathrm{depth}_i}$: the exponential of the maximum over the finite family is bounded by one plus the sum of the exponentials (`two_pow_sup_le_one_add_sum`). Averaging this inequality and using monotonicity of the random-restriction average gives $\mathbb E[2^D]\le 1+\sum_i\mathbb E[2^{\mathrm{depth}_i}]\le1+2m$. The equality that moves the finite sum through the average follows from additivity and finite-sum linearity of that average. Applying the pointwise estimate and averaging once more yields $\mathbb E[D]\le q+2^{-q}(1+2m)$. Since $1+2m\le2(m+1)\le2^{q+1}$, the last term is at most $2$, proving the claim.

**Key facts.** `FABL.natCast_le_add_pow_div_pow`, `FABL.two_pow_sup_le_one_add_sum`, `FABL.expectRandomRestriction_mono`, `FABL.expectRandomRestriction_add`, `FABL.expectRandomRestriction_const`, `FABL.sum_expectRandomRestriction`.
