<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.uniformRandomizedAssignment_expectedValue_maxLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value for Linear Constraints

**Claim.** For the stated Max-Linear instance, the expected fraction of satisfied constraints under a uniform assignment of elements of $\mathbb{F}_2$ to the variables is $1/2$.

**Proof.** The independent uniform assignment has the uniform law on the set of all assignments (`uniformRandomizedAssignment_sampleLaw`), and expectation under this uniform PMF agrees with the uniform expectation (`pmfExpectation_uniformPMF_eq_expect`). The uniform expected value of the given Max-Linear instance is $1/2$ (`expect_value_maxLinear`). Mapping this rational expectation into the reals gives the equality in the theorem.

**Key facts.** `FABL.uniformRandomizedAssignment_sampleLaw`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_value_maxLinear`.
