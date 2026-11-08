<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.innerProductModTwoSupportDensity_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support-Density Expectation

**Claim.** For every positive natural number $m$, the expectation under the support density of the indicator of the event that the two length-$m$ blocks have inner product modulo two equal to $1$ is $1$.

**Proof.** Let $p$ be the uniform probability of the inner-product-one event. Its explicit value is $(1-2^{-m})/2$ (\texttt{uniformProbability_innerProductModTwoOneSet}), so $p>0$. By the pointwise support-density formula (\texttt{innerProductModTwoSupportDensity_apply}), the density is $p^{-1}$ times the event indicator. Multiplying by the same indicator in the expectation leaves that indicator unchanged, since its values are $0$ and $1$; this uses the fact that every element of $\mathbb F_2$ is either $0$ or $1$ (\texttt{f₂_eq_zero_or_one}). The expectation therefore equals $p^{-1}$ times the uniform expectation of the indicator. That expectation is $p$, so the result is $p^{-1}p=1$.

**Key facts.** `FABL.uniformProbability_innerProductModTwoOneSet`, `FABL.innerProductModTwoSupportDensity_apply`, `FABL.f₂_eq_zero_or_one`, `FABL.expect_booleanRealEmbedding_innerProductModTwoBit`.
