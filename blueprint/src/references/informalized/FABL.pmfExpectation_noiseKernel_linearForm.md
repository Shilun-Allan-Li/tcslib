<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.pmfExpectation_noiseKernel_linearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise expectation of a linear form

**Claim.** Under the coordinatewise noise distribution with correlation parameter $\rho$, the expected value of the linear form with coefficients $a_i$ is $\rho$ times its value at the original sign vector $x$.

**Proof.** Expand the linear form as the finite sum of its coordinate contributions and interchange that sum with expectation. For each coordinate, factor out its coefficient $a_i$ using the fact that expectation scales by constants (`pmfExpectation_const_mul`). The coordinate sign function is the degree-one monomial on the singleton set $\{i\}$. The noise expectation of a monomial on a set $S$ is $\rho^{|S|}$ times its value at the original vector (`pmfExpectation_noiseKernel_monomial`); for a singleton this gives $\rho\,\mathrm{signValue}(x_i)$. Thus the sum becomes $\sum_i a_i\rho\,\mathrm{signValue}(x_i)$, which factors as $\rho$ times the original linear form.

**Key facts.** `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_noiseKernel_monomial`.
