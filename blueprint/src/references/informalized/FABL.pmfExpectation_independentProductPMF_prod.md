<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_independentProductPMF_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Expectation Under Independence

**Claim.** Under an independent product distribution, the expectation of the product of coordinate functions is the product of their individual expectations.

**Proof.** Expand the expectation as a finite sum over all coordinate tuples. At each tuple, the probability mass is the product of the coordinate masses, by the defining formula for the independent product distribution (\texttt{FABL.independentProductPMF\_apply}). Taking the real value of that mass turns it into the product of the real coordinate masses. Thus the summand is the product, over all indices, of the individual terms $(p_i(x_i))_{\mathbb R}q_i(x_i)$. The finite product-of-sums identity then factors the sum over tuples into the product of the coordinate sums. Each coordinate sum is exactly the expectation of $q_i$ under $p_i$, proving the formula.

**Key facts.** `FABL.independentProductPMF_apply`.
