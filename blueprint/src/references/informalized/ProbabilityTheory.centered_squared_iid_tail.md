<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean :: ProbabilityTheory.centered_squared_iid_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-sided concentration for centered squares

**Claim.** For a finite independent family, if each centered square $(Y_i)^2-\sigma^2$ has a Bernstein moment-generating-function bound with parameters $c,t_{\rm max}$, then the absolute deviation of the sum of squares from $|\iota|\sigma^2$ has the stated two-sided tail bound for $0\le s\le 2|\iota|ct_{\rm max}$.

**Proof.** Set $S_i=Y_i^2-\sigma^2$. Measurability is preserved by squaring and subtracting a constant, and independence is preserved by applying this same measurable function to each variable. The independent-sum theorem therefore gives a Bernstein moment-generating-function bound for $\sum_i S_i$ with quadratic parameter $|\iota|c$ and range parameter $t_{\rm max}$. Pointwise, $\sum_i S_i=\sum_iY_i^2-|\iota|\sigma^2$, so the event in the claim is exactly the event that the absolute value of this centered sum exceeds $s$. If the index set is empty, the sum and its deviation are zero, and the event is empty because $s\ge0$. Otherwise, apply the two-sided tail estimate for a Bernstein moment-generating-function bound with parameter $|\iota|c>0$; the assumed upper limit on $s$ is precisely the range condition for that estimate. This gives the claimed bound.

**Key facts.** `ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun`, `ProbabilityTheory.HasBernsteinMGF.measure_abs_gt_le`.
