<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/Influence.lean :: BooleanAnalysis.Hypercontractivity.indicator_linear_form_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Correlation with a Linear Form

**Claim.** For an indicator-valued function of positive expectation $\alpha$ and a normalized coefficient vector, the squared correlation with the associated sign-valued linear form is at most $2\alpha^2\log(1/\alpha)$.

**Proof.** Let $L(x)=\sum_i a_i(-1)^{x_i}$ and let $c=\mathbb E[fL]$. The Rademacher moment-generating-function bound (`rademacher_mgf_le`) and the normalization $\sum_i a_i^2=1$ give $\mathbb E e^{tL}\le e^{t^2/2}$. Apply the indicator pairing estimate `indicator_innerProduct_le_of_mgf` with $t=c/\alpha$ and $b=t^2/2$. This gives an inequality which, after multiplying by the positive quantity $2\alpha$ and rearranging, reads $c^2+2\alpha^2\log\alpha\le0$. Since $\log(1/\alpha)=-\log\alpha$, this is exactly the claimed bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.indicator_innerProduct_le_of_mgf`, `BooleanAnalysis.ThresholdFunctions.rademacher_mgf_le`.
