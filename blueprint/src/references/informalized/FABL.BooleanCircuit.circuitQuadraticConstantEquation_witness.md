<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticConstantEquation_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Witness Satisfies the Constant Equation

**Claim.** The vector encoding the constant coordinate, input assignment, and gate values satisfies the circuit’s homogeneous quadratic equation that fixes the constant coordinate to one.

**Proof.** The equation is defined by a list of quadratic terms, so the satisfaction criterion for an equation built from terms says that its value on a vector is the sum of the corresponding coordinate products, equal to the right-hand side (FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff). For the constant equation, the list consists of the constant coordinate paired with itself and the right-hand side is one. In the witness vector that coordinate is one, so the sole product is one, as required.

**Key facts.** `FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`.
