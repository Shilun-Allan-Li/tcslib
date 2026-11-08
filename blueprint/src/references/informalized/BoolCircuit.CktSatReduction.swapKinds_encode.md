<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.swapKinds_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Respects Gate Duality

**Claim.** For every directed acyclic circuit $C$, applying the bit-string transformation that swaps AND and OR gate kinds to the encoding of $C$ gives the encoding of the circuit obtained by exchanging AND and OR at every gate while leaving NOT gates and all gate arguments unchanged.

**Proof.** The transformation leaves each initial run of true bits in the unary encoding unchanged: while it reads such a run, its state remains the initial state and true bits are preserved (`T_ones`). After the input-count encoding, it is therefore in the state that parses the gate list. On the encoded gates, the transformation sends the encoding of each gate to the encoding of its dual, preserving its arguments and exchanging AND with OR while fixing NOT (`T_gates`). The transformation processes the remaining bits according to its one-bit transition rule (`T_cons`); in this final output-vertex encoding it leaves the bits unchanged. Together, these blocks give exactly the encoding of the dual circuit.

**Key facts.** `BoolCircuit.CktSatReduction.T_ones`, `BoolCircuit.CktSatReduction.T_gates`, `BoolCircuit.CktSatReduction.T_cons`.
