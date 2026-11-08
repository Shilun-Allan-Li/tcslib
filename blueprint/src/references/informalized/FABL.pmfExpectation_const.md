<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a constant

**Claim.** For a probability mass function on a finite set, the expectation of the constant function with value $c$ is $c$.

**Proof.** Express the constant function as $c$ times the constant function one. By the scaling rule for expectation (`FABL.pmfExpectation_const_mul`), its expectation is $c$ times the expectation of one. The latter is one because the probabilities sum to one (`FABL.pmfExpectation_const_one`), so the result is $c$.

**Key facts.** `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_const_one`.
