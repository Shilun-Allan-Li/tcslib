<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_selectorCoordinatePairPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Equality of Selector Pair Expectations

**Claim.** The selector-based procedure and the procedure that retains the first sampled value with probability $(1+\theta)/2$ give the same expectation of $H$.

**Proof.** Expand the successive sampling steps using the expectation-under-binding and expectation-under-mapping formulas (`pmfExpectation_bind`, `pmfExpectation_map`). The correlated signs have four possible pairs: $(1,1)$ and $(-1,-1)$ each have weight $(1+\theta)/4$, while $(1,-1)$ and $(-1,1)$ each have weight $(1-\theta)/4$ (`pmfExpectation_correlatedSignPairPMF_eq_four_values`). Consequently, after averaging over the two initially sampled values, the selector procedure gives weight $(1+\theta)/2$ to the diagonal contribution $\mathbb{E}_{x\sim\pi}H(x,x)$ and weight $(1-\theta)/2$ to the independent-pair contribution $\mathbb{E}_{x\sim\pi}\mathbb{E}_{y\sim\pi}H(x,y)$. In identifying the two mixed terms, interchange the order of the two finite expectations and rename the variables (`pmfExpectation_swap`).

For the retention procedure, conditional on the first value $x$, the second value is retained as $x$ with probability $\theta$ in the stated retention parameterization, and is independently resampled otherwise; the expectation of this coordinate-noise step is the corresponding weighted sum (`pmfExpectation_productCoordinateNoisePMF`). Averaging over $x$ and using linearity and the fact that expectation of a constant is that constant (`pmfExpectation_two_linear`, `pmfExpectation_const`) yields the same diagonal and independent-pair contributions with the same coefficients. Since the retention parameter is $(1+\theta)/2$, these are precisely the coefficients obtained from the selector calculation.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_correlatedSignPairPMF_eq_four_values`, `FABL.pmfExpectation_productCoordinateNoisePMF`, `FABL.pmfExpectation_four_linear`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_swap`, `FABL.pmfExpectation_two_linear`.

**Caveat.** The supplied Lean proof uses `pmfExpectation_four_linear` and `pmfExpectation_const` to simplify the four terms, but its final identification with the retention expression is encoded in algebraic rewrites. The account follows those rewrites; the two contribution decompositions are not separately stated as upstream lemmas.
