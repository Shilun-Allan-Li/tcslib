<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinate_abs_third_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third moment bound for a coordinate derivative

**Claim.** Under the stated independence, hypercontractivity, centering, and variance assumptions, the third absolute moment of $X_i$ times the random-input evaluation of the coordinate derivative polynomial is at most $(1/\rho)^{3k}\,\mathrm{Inf}_i[F_{\mathrm{cube}}]^{3/2}$.

**Proof.** 1. Remove from $F$ its coordinate-free part by defining $G(S)=F(S)-\operatorname{coordinateFree}(F,i)(S)$. The coordinate-free part vanishes on sets containing $i$ and agrees with $F$ on other sets. Thus $G$ vanishes off sets containing $i$ and agrees with $F$ on sets containing $i$. In particular, every coefficient of $G$ on a set larger than $k$ is zero: for such a set containing $i$ this follows from the degree bound on $F$, and otherwise the coefficient of $G$ is zero. Hence $G$ has degree at most $k$.

2. The evaluation of $G$ is the difference between the evaluations of $F$ and its coordinate-free part. Splitting the evaluation of $F$ into its coordinate-free contribution and its coordinate-$i$ contribution (the coordinate evaluation split) identifies this difference with $X_i$ times the evaluation of the coordinate derivative polynomial.

3. By the influence Fourier identity, influence is the sum of squared Fourier coefficients over sets containing $i$. The coefficient description of $G$ shows that its squared-coefficient sum is exactly this same sum: on sets containing $i$, its coefficients are those of $F$; elsewhere they vanish. Apply the polynomial third-moment bound to $G$, using its degree bound and the given probabilistic hypotheses. It bounds the third absolute moment of its random-input evaluation by $(1/\rho)^{3k}$ times its squared-coefficient sum to the power $3/2$. The two identifications above turn this into the asserted inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.eval_coordinate_split`, `BooleanAnalysis.influence_eq_sum_fourier`, `BooleanAnalysis.GaussianSpace.Invariance.polynomial_abs_third_moment`.
