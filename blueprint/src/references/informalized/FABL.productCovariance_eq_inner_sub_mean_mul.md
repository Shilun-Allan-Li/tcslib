<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCovariance_eq_inner_sub_mean_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance and product inner product

**Claim.** The covariance of $f$ and $g$ equals their product inner product minus the product of their means.

**Proof.** Write each centered function as $f-\mathbb E f$ and $g-\mathbb E g$, and expand their product pointwise as $fg-(\mathbb E g)f-(\mathbb E f)g+\mathbb E f\,\mathbb E g$. Expectation is additive, sends a scalar multiple of a function to that scalar times its expectation, and sends a constant function to its constant value (`pmfExpectation_add_fun`, `pmfExpectation_smul_fun`, and `pmfExpectation_const`). Applying these facts to the expansion gives $\mathbb E[fg]-(\mathbb E f)(\mathbb E g)$, which is the asserted product inner product minus the product of the means.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_smul_fun`, `FABL.pmfExpectation_const`.
