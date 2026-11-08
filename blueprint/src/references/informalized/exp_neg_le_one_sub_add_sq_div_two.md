<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: exp_neg_le_one_sub_add_sq_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bound for the negative exponential

**Claim.** For every $x\ge 0$, $e^{-x}\le 1-x+x^2/2$.

**Proof.** The standard lower quadratic bound for the exponential gives $1+x+x^2/2\le e^x$ when $x\ge0$. Also $1-x+x^2/2\ge0$, since it equals $((x-1)^2+1)/2$. Multiplying the lower bound by this nonnegative quantity preserves the inequality. The product of the two quadratic expressions is $1+x^4/4$. Thus $e^x(1-x+x^2/2)\ge 1+x^4/4\ge1$. Since $e^x>0$, taking reciprocals in this inequality yields $e^{-x}\le1-x+x^2/2$.
