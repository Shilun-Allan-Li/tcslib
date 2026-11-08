<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedPairPMF_expect_signValue_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-coordinate mean

**Claim.** For every coordinate of the first sign vector in a correlated pair, the expected sign is zero.

**Proof.** Apply the expectation rule for a two-stage sample ( `pmfExpectation_bind`): first average over the uniform vector $x$, then over the noise output $y$. For fixed $x$, the tested quantity depends only on the first component of $(x,y)$, so its conditional expectation is the constant $x_i$; this follows from the expectation of a constant (`pmfExpectation_map`, `pmfExpectation_const`). The remaining average is therefore the uniform-cube expectation of the coordinate function $x\mapsto x_i$. This function is the singleton monomial indexed by $\{i\}$, whose uniform expectation is zero because the indexing set is nonempty (`expect_monomial`).

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_monomial`.
