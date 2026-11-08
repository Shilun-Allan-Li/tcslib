<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.uniformRandomizedAssignment_expectedValue_maxE3Sat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value for Max-3-SAT

**Claim.** For a Max-3-SAT instance, the expected fraction of satisfied clauses under a uniform assignment of Boolean values to the variables is $7/8$.

**Proof.** The sample law of the independent uniform assignment is the uniform law on all assignments (`uniformRandomizedAssignment_sampleLaw`). Its PMF expectation is therefore the uniform expectation (`pmfExpectation_uniformPMF_eq_expect`). The expected value of a Max-3-SAT instance under a uniform assignment is $7/8$ (`expect_value_maxE3Sat`). Viewing this rational-valued expectation as real yields the claimed equality.

**Key facts.** `FABL.uniformRandomizedAssignment_sampleLaw`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_value_maxE3Sat`.
