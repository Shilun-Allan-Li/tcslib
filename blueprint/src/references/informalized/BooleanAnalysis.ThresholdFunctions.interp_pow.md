<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.interp_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Form of Interpolation

**Claim.** Under the stated nonnegativity assumptions, the interpolation bound implies $M^{2(m+1)}\le A^2B^{2m}$.

**Proof.** Raise the assumed inequality to the natural power $m+1$. Since both sides are nonnegative, this preserves the inequality. The power of the product becomes the product of the powers; the exponents $(m+1)/(m+1)$ and $m(m+1)/(m+1)$ reduce the two real powers to $A$ and $B^m$, respectively. Thus $M^{m+1}\le AB^m$. Squaring this inequality preserves its order, and gives $M^{2(m+1)}\le A^2B^{2m}$.
