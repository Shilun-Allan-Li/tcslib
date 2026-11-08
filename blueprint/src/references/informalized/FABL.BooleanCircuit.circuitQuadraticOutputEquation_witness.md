<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticOutputEquation_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Equation for an Accepting Witness

**Claim.** If the circuit accepts an input, then the canonical witness formed from that input and the evaluated gate values satisfies the circuit’s quadratic output equation.

**Proof.** The output equation is represented by two terms: the output-gate variable times the constant variable, and the constant variable squared. On the canonical witness, the constant variable is $1$ and the output-gate variable is the field encoding of the evaluated output (`circuitQuadraticWitness_constant`, `circuitQuadraticWitness_gate`). The equation’s left side is consequently the encoded output plus $1$. Acceptance says the output is true, whose encoding is $1$, so this sum is zero in characteristic two. The correspondence between the equation and its sum of terms is `homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`.

**Key facts.** `FABL.homogeneousQuadraticEquationOfTerms_satisfiedBy_iff`, `FABL.BooleanCircuit.circuitQuadraticWitness_constant`, `FABL.BooleanCircuit.circuitQuadraticWitness_gate`.
