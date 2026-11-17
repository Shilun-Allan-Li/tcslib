<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.gaussianQuadrantProbability_one_sub_upperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-Left Quadrant Symmetry

**Claim.** For $-1<\rho<1$, evaluating the Gaussian quadrant probability at the complementary upper-tail parameter gives the probability that both correlated Gaussian coordinates are at most $t$.

**Proof.** Unfold the quadrant probability. The upper quantile at the complement of a parameter is the negative of the upper quantile at that parameter (\texttt{standardGaussianUpperQuantile\_one\_sub}). For the parameter given by the standard Gaussian upper tail at $t$, its upper quantile is $t$ (\texttt{standardGaussianUpperQuantile\_upperTailOpen\_biasedMajority}); hence the quantile at the complementary parameter is $-t$. Finally, central symmetry of the correlated Gaussian measure identifies the probability that both coordinates exceed $-t$ with the probability that both are at most $t$ (\texttt{correlatedGaussianMeasure\_upperRight\_neg\_eq\_lowerLeft}).

**Key facts.** `FABL.standardGaussianUpperQuantile_one_sub`, `FABL.standardGaussianUpperQuantile_upperTailOpen_biasedMajority`, `FABL.correlatedGaussianMeasure_upperRight_neg_eq_lowerLeft`.
