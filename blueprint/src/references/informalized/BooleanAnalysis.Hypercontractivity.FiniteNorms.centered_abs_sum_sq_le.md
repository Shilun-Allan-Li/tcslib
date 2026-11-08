<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.centered_abs_sum_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered absolute-moment estimate

**Claim.** For nonnegative weights and a weighted-mean-zero function on a finite set, the square of its weighted absolute first moment is at most four times its weighted second moment multiplied by the total weight on the positive set.

**Proof.** Let $I_i$ be the indicator of the condition $g_i>0$. Since the weighted mean of $g$ is zero, the weighted sum of $|g_i|$ equals twice the weighted sum of $g_i I_i$: termwise, $2g_iI_i-g_i=|g_i|$ whether $g_i$ is positive or nonpositive, and the weighted sum of the subtracted $g_i$ vanishes. Apply the finite weighted Cauchy–Schwarz inequality to the factors represented by $w_i g_i I_i$, $w_i g_i^2$, and $w_i I_i$. Its pointwise hypotheses follow from $w_i\ge0$ and $I_i\in\{0,1\}$, and it gives $(\sum_i w_i g_i I_i)^2\le(\sum_i w_i g_i^2)(\sum_i w_i I_i)$. Squaring the preceding identity and multiplying this bound by four proves the result, since $I_i$ is precisely the indicator of $g_i>0$.
