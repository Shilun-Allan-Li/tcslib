<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_const_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of One

**Claim.** For a probability mass function on a finite set, the expectation of the constant function with value $1$ is $1$.

**Proof.** Equip the finite set with its discrete measurable structure and rewrite the finite-sum expectation as an integral against the probability measure associated to the mass function (the expectation–integral identity, `FABL.pmfExpectation_eq_integral`). The integral of the constant function $1$ is the total mass of that measure, which is $1$.

**Key facts.** `FABL.pmfExpectation_eq_integral`.
