<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.hc_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural-Power Form of a Moment Comparison

**Claim.** Let $m,k$ be natural numbers and $B,M,D$ be nonnegative real numbers. If $D^kB\le M^{2(m+1)/(2m+1)}$, then $(D^kB)^{2m+1}\le M^{2(m+1)}$.

**Proof.** Both sides of the assumed inequality are nonnegative, so raising them to the natural power $2m+1$ preserves the inequality. The right-hand side becomes $(M^{2(m+1)/(2m+1)})^{2m+1}$. For nonnegative $M$, the laws of real powers combine these exponents, giving $M^{(2(m+1)/(2m+1))(2m+1)}=M^{2(m+1)}$. Thus the powered inequality is exactly the desired one.
