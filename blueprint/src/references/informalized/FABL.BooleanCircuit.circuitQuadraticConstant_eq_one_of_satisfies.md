<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticConstant_eq_one_of_satisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Coordinate of a Satisfying Assignment

**Claim.** Any assignment satisfying the circuit’s homogeneous quadratic system has constant coordinate equal to one.

**Proof.** The constant equation is one of the equations in the system, so the assumed system satisfaction implies that this equation is satisfied. The criterion for satisfaction of an equation defined by terms (FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff) reduces it here to the square of the constant coordinate being one. In , every element is its own square, since the field has two elements. Therefore the constant coordinate itself equals one.

**Key facts.** `FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`.
