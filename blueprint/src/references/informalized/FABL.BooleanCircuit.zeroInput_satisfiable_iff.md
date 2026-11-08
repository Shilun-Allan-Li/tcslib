<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.zeroInput_satisfiable_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability with no input bits

**Claim.** A Boolean circuit with no input bits is satisfiable if and only if it accepts the unique assignment on the empty set of input coordinates.

**Proof.** If the circuit is satisfiable, some assignment $w$ makes it accept. There is only one function from the empty set of input coordinates to the Boolean values, so $w$ equals the specified empty assignment; consequently, that assignment is accepted. Conversely, if the specified assignment is accepted, it itself witnesses satisfiability.
