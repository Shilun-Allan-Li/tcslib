<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.degree_norm_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint of norm comparisons

**Claim.** Let $k$ be a nonnegative integer and $A,B\in\mathbb R$. If $B\le((1+1/m)^{m+1})^{2k}A^2$ for every integer $m\ge2$, then $B\le e^{2k}A^2$.

**Proof.** The comparison factors converge to $e^{2k}$ as $m\to\infty$ (degree_norm_limit). Multiplying this convergent sequence by the fixed number $A^2$ shows that the right-hand sides converge to $e^{2k}A^2$. The assumed inequalities hold for every $m\ge2$, hence eventually along the sequence. The order limit principle says that if a sequence is eventually at least $B$ and converges to a real number, then its limit is at least $B$. Applying it gives $B\le e^{2k}A^2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.degree_norm_limit`.
