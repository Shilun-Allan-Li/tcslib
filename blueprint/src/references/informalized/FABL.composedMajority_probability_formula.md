<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.composedMajority_probability_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Probability Formula

**Claim.** For every $m\ge 0$ and $0<p<1$, the biased minus-probability polynomial of the composed majority satisfies $P_{\mathrm{comp}}(p)=p^2+2p(1-p)P_{\mathrm{maj}}(p)$, where $P_{\mathrm{maj}}$ is the polynomial for majority on $2m+1$ coordinates.

**Proof.** Write $A$ and $B$ for the indicators that the two head signs are $-1$, and $C$ for the indicator that the tail majority is $-1$. The three-input majority has minus-indicator $AB+AC+BC-2ABC$ (`majorityThreeValue_neg_indicator`). Averaging first over the tail, the expectation of $C$ is the tail majority probability, while $A$ and $B$ are fixed; linearity of expectation therefore gives $AB+(A+B-2AB)P_{\mathrm{maj}}(p)$. The head coordinates are independent biased signs: each minus-indicator has mean $p$ (`productMean_headIndicator`), and their product has mean $p^2$ (`productMean_headIndicator_mul`). Averaging the displayed expression over the head yields $p^2+(2p-2p^2)P_{\mathrm{maj}}(p)$, which is the claimed formula. The identification of the polynomial probabilities with the corresponding distributional probabilities uses `biasedMinusProbabilityPolynomial_eq`; evaluating the split distribution is justified by the iterated-expectation identity (`pmfExpectation_bind`), and the expectation is transported through the tail map by `pmfExpectation_map`. Linearity and scaling of expectation supply the remaining rearrangement.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.majorityThreeValue_neg_indicator`, `FABL.productMean_headIndicator`, `FABL.productMean_headIndicator_mul`, `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_smul_fun`, `FABL.pmfExpectation_sub_general`, `FABL.composedMajoritySplitProbability_eq_biasedMinusProbability`.
