<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.acceptedProperty_zero_universal_or_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance with No Input Bits

**Claim.** For a Boolean circuit with zero input bits, either every input assignment is accepted or none is accepted.

**Proof.** There is only one assignment to a set of zero input bits. Call it the empty assignment. If the circuit accepts it, then every assignment is equal to it and is accepted. If it does not accept it, then every assignment equals it and is rejected. These two cases give the stated alternative.
