<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInput_accepted_of_satisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from a Satisfying Assignment

**Claim.** If an assignment satisfies the circuit’s homogeneous quadratic system, then the circuit accepts the input obtained by decoding its input variables.

**Proof.** Satisfaction of the constant equation forces the constant variable to equal $1$ (`circuitQuadraticConstant_eq_one_of_satisfies`). Satisfaction of each gate equation ensures that its assigned gate variable equals the value obtained by evaluating that gate on the decoded input; in particular this holds for the output gate (`circuitQuadraticGateValue_eq_evalGate_of_satisfies`). The output equation says that the product of the output variable and the constant variable, plus the square of the constant variable, is zero. Using the constant value $1$ and the output-gate evaluation, this says that the output bit plus $1$ is zero in $\mathbb F_2$. Hence the output bit is $1$, which means the circuit accepts. The translation from a quadratic equation built from terms to the corresponding sum of products is given by `homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`.

**Key facts.** `FABL.BooleanCircuit.circuitQuadraticConstant_eq_one_of_satisfies`, `FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`, `FABL.BooleanCircuit.circuitQuadraticGateValue_eq_evalGate_of_satisfies`.
