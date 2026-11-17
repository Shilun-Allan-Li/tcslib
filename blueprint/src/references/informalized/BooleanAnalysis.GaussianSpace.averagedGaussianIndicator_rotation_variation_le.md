<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_rotation_variation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging Contracts Rotation Variation

**Claim.** For a measurable set, the expected absolute change of its Gaussian-averaged indicator under a rotation is at most the probability that the original indicator disagrees across that rotation.

**Proof.** Let $\mu$ be the standard Gaussian product measure on $\mathbb R^n$, and write $R_a(x,y)=\cos(a)x+\sin(a)y$. First, for each pair $(x,x')$, the difference between the two averages over independent Gaussian vectors is bounded by the measure of the set of averaging pairs on which the corresponding indicators disagree (the pairwise disagreement bound, `averagedGaussianIndicator_pair_diff_le`). Integrating this pointwise estimate over $(x,x')$ and applying Tonelli's theorem identifies the resulting iterated measure with the probability of disagreement between $1_A(R_u(X,Y))$ and $1_A(R_u(R_v(X,X'),R_v(Y,Y')))$. The disagreement set is measurable because $A$ is measurable and the rotation maps are measurable (`measurableSet_indicatorDisagreement`). Finally, rotations in the two independent coordinate pairs commute: $R_u(R_v(X,X'),R_v(Y,Y'))=R_v(R_u(X,Y),R_u(X',Y'))$. The paired Gaussian endpoint map preserves product Gaussian measure, so this last disagreement probability equals the probability that the indicators at a standard Gaussian pair and its $v$-rotation disagree, namely $R_A(v)$ (`measurePreserving_gaussianPairedEndpoint`).

**Key facts.** `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_pair_diff_le`, `BooleanAnalysis.GaussianSpace.measurableSet_indicatorDisagreement`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianPairedEndpoint`.
