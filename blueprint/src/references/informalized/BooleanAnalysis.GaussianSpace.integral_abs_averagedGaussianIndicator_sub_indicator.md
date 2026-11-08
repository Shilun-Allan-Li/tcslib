<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.integral_abs_averagedGaussianIndicator_sub_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Approximation and Rotation Sensitivity

**Claim.** For measurable $A\subseteq\mathbb R^n$ and any angle $\theta$, the mean absolute difference between the averaged indicator $u_\theta$ and $1_A$ equals the probability that membership in $A$ changes under the Gaussian rotation.

**Proof.** Let $\mu=\gamma_n$, and let $R(x,y)=\cos\theta\,x+\sin\theta\,y$. The set $E$ of pairs $(x,y)$ for which exactly one of $x$ and $R(x,y)$ belongs to $A$ is measurable; this is the indicator-disagreement measurability fact (`measurableSet_indicatorDisagreement`). By integrating its sections, the product measure of $E$ is the integral over $x$ of the measure of the section $E_x=\{y:(x,y)\in E\}$. For fixed $x$, put $S=\{y:R(x,y)\in A\}$. The averaged indicator is $\mu(S)$, by the identity expressing it as the measure of the rotated preimage (`averagedGaussianIndicator_eq_real_measure`). If $x\in A$, then $E_x=S^c$, so its measure is $1-\mu(S)$, since $\mu$ is a probability measure. This equals $|\mu(S)-1|=|u_\theta(x)-1_A(x)|$, using $0\leq\mu(S)\leq1$. If $x\notin A$, then $E_x=S$, whose measure is $\mu(S)=|u_\theta(x)-0|$. Thus in both cases the section measure is the stated absolute difference. Integrating over $x$ proves the identity, and the product measure of $E$ is precisely the rotation sensitivity.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurableSet_indicatorDisagreement`, `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_real_measure`.
