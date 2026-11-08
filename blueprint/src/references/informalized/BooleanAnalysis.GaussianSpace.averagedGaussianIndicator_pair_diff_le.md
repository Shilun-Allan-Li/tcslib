<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_pair_diff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coupled Bound for Averaged Indicators

**Claim.** For measurable $A$, the absolute difference between the two averaged indicators in the statement is bounded by the probability, under two independent standard Gaussian vectors, that the corresponding two membership indicators disagree.

**Proof.** Let $\mu$ be the standard Gaussian product law on $\mathbb R^n$, and write $R_t(z,w)=\cos(t)z+\sin(t)w$. For fixed $z$, let $S(z)=\{y:R_u(z,y)\in A\}$. The averaged-indicator-as-measure identity (`averagedGaussianIndicator_eq_real_measure`) identifies the two averaged indicators with $\mu(S(x))$ and $\mu(S(R_v(x,x')))$. On the product space with law $\mu\times\mu$, take the events $C=\{(z,w):w\in S(x)\}$ and $D=\{(z,w):R_v(z,w)\in S(R_v(x,x'))\}$. The first coordinate projection preserves the product law, so the probability of $C$ is $\mu(S(x))$. The rotation map $(z,w)\mapsto R_v(z,w)$ preserves the product Gaussian law (`measurePreserving_gaussianRotation`), so the probability of $D$ is $\mu(S(R_v(x,x')))$.

For any two events in a finite measure space, the absolute difference of their measures is at most the measure of their symmetric difference (`abs_measureReal_sub_le_symmDiff`). Here, membership in $C$ and $D$ is exactly agreement of the two displayed membership conditions in the question. Their symmetric difference is therefore the event that those indicators disagree, giving the asserted bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_real_measure`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`, `BooleanAnalysis.GaussianSpace.abs_measureReal_sub_le_symmDiff`.
