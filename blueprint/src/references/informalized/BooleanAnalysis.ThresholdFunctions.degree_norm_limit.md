<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.degree_norm_limit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Limit of finite degree factors

**Claim.** For every natural number $k$, the sequence $((1+1/m)^{m+1})^{2k}$ converges to $e^{2k}$ as $m$ tends to infinity.

**Proof.** The sequence $1+1/m$ tends to $1$, since $1/m$ tends to zero. Also, the standard exponential limit gives $(1+1/m)^m\to e$. Multiplying these two convergent sequences shows that $(1+1/m)^{m+1}\to e\cdot1=e$. Taking the fixed natural power $2k$ preserves convergence, so the limit is $e^{2k}$, using the identity $(e)^q=e^q$ for natural $q$.
