<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.uniformRandomizedAssignment_expectedValue_maxE3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value for Max-3-Lin

**Claim.** For a Max-3-Lin instance, the expected fraction of satisfied constraints under a uniform assignment of elements of $\mathbb{F}_2$ to the variables is $1/2$.

**Proof.** The sample law of the independent uniform assignment is the uniform law on all assignments (`uniformRandomizedAssignment_sampleLaw`). Under a uniform law, the PMF expectation agrees with the uniform expectation (`pmfExpectation_uniformPMF_eq_expect`). The expected value of a Max-3-Lin instance under a uniform assignment is $1/2$ (`expect_value_maxE3Lin`). Passing that rational-valued expectation through the inclusion $\mathbb{Q}\to\mathbb{R}$ gives the stated real-valued expectation.

**Key facts.** `FABL.uniformRandomizedAssignment_sampleLaw`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_value_maxE3Lin`.

**Caveat.** The informal statement also mentions a Max-E3-Sat approximation guarantee, but the formal theorem and proof establish only the Max-3-Lin expected value.
