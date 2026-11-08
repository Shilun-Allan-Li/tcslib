<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.pmfExpectation_correlatedPairPMF_linearForm_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Expectation of Linear Forms

**Claim.** For a uniform sign vector $X$ and its $rho$-correlated noisy vector $Y$, the expectation of the product of their linear forms is $\rho\sum_i a_i^2$.

**Proof.** First condition on the initial vector $X=x$ by expanding the joint expectation as an iterated expectation (`FABL.pmfExpectation_bind`). For this fixed $x$, the map from the noisy vector $y$ to $(x,y)$ lets us view the integrand as $L_a(x)L_a(y)$ (`FABL.pmfExpectation_map`), where $L_a$ is the linear form with coefficients $a_i$. Pulling out the fixed factor $L_a(x)$ and using the mean of the linear form under the noise kernel gives the conditional expectation $\rho L_a(x)^2$ (`FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_noiseKernel_linearForm`). Now average over uniform $x$: pull out $\rho$, identify uniform expectation with the usual cube expectation (`FABL.pmfExpectation_uniformPMF_eq_expect`), and use the second-moment identity $\mathbb{E}[L_a(X)^2]=\sum_i a_i^2$ (`FABL.expect_linearForm_sq`).

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_noiseKernel_linearForm`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_linearForm_sq`.
