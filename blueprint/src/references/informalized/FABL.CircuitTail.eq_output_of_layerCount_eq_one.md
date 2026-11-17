<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.CircuitTail.eq_output_of_layerCount_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A single layer is the output layer

**Claim.** If a circuit tail has layer count $1$, then it is an output layer for some finite set of incoming wires.

**Proof.** Proceed by the two constructors of a circuit tail. If the tail is already an output layer, its incoming wire set gives the required representation. Otherwise it has the form of a layer followed by a remaining tail. Its layer count is one plus the remaining tail's layer count, while every tail has layer count at least one (`CircuitTail.one_le_layerCount`). Therefore this case has layer count at least two, contradicting the assumed count of one. Only the output-layer case remains.

**Key facts.** `FABL.CircuitTail.one_le_layerCount`.
