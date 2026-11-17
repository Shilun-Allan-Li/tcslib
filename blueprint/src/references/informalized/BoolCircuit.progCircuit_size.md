<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the program circuit

**Claim.** The program circuit's size equals $n+2$ plus the sum of the gadget widths for the instructions in the program.

**Proof.** Unfold circuit size and the circuit's gate list, reducing the claim to the established length formula for the program gates (BoolCircuit.length_progGates) at the full program length. That formula identifies the number of input vertices plus the number of gates with the base offset, as required.

**Key facts.** `BoolCircuit.length_progGates`.
