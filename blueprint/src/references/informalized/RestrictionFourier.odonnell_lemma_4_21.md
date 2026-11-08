<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/FourierConcentration.lean :: RestrictionFourier.odonnell_lemma_4_21 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Tail Bound Under Random Restrictions

**Claim.** For a Boolean function $f$, a parameter $p$ with $0\le p\le1$, and an integer $k\ge1$, the sum of squared Fourier coefficients over sets $U$ satisfying $3k\le p|U|$ is at most four times the Bernoulli restriction probability that the restricted function has decision-tree depth at least $k$.

**Proof.** 1. Fix a restriction $\rho$. If the restricted function has decision-tree depth at least $k$, its Fourier tail over sets of size at least $k$ is bounded by its total Fourier mass, which is $1$ by Parseval for a $\{-1,1\}$-valued function (`BooleanAnalysis.parseval_pm_one`). If its depth is less than $k$, the degree bound by decision-tree depth (`DecisionTree.degree_le_dtDepth`) makes every Fourier coefficient on a set of size at least $k$ vanish. Hence the restricted tail is at most the indicator of depth at least $k`.

2. Average this pointwise bound over restrictions with their Bernoulli weights, which are nonnegative (`SwitchingLemma.bernoulliRestrWeight_nonneg'`). Interchanging the finite sums and using the identity that expresses the average restricted Fourier tail as the original Fourier mass weighted by the probability of retaining at least $k$ variables from each set (`RestrictionFourier.sum_tail_expectation_eq`) bounds that weighted mass by the probability of depth at least $k`.

3. For each set $U$ with $3k\le p|U|$, the probability that its intersection with the free variables has size at least $k$ is at least $1/4$ (`RestrictionFourier.bernoulliRestrProb_card_inter_ge`). Multiplying by the nonnegative squared Fourier coefficient shows that its contribution to the desired tail is at most four times its contribution to the weighted mass. For sets failing the threshold, the desired summand is zero; nonnegativity of their weighted contributions follows from nonnegativity of restriction probabilities (`RestrictionFourier.bernoulliRestrProb_nonneg`). Summing these comparisons and applying the averaged bound proves the claimed inequality.

**Key facts.** `BooleanAnalysis.parseval_pm_one`, `DecisionTree.degree_le_dtDepth`, `SwitchingLemma.bernoulliRestrWeight_nonneg'`, `RestrictionFourier.sum_tail_expectation_eq`, `RestrictionFourier.bernoulliRestrProb_card_inter_ge`, `RestrictionFourier.bernoulliRestrProb_nonneg`.

**Caveat.** The supplied informal statement gives a concentration conclusion with a factor of 3 and threshold $3k/\delta$. The formal declaration and proof instead establish the displayed Fourier-tail inequality with factor 4 and threshold $3k\le p|U|$; the account follows that formal proof.
