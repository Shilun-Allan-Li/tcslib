<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.toBooleanFunction_hasDNFWidthLE_or_hasCNFWidthLE_of_depth_eq_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-two width representation

**Claim.** If a depth circuit has depth two, then its computed Boolean function has either a DNF representation or a CNF representation whose width is at most the circuit's width.

**Proof.** The circuit depth is one plus the number of layers in its tail. Hence depth two forces the tail to have exactly one layer. A tail with one layer is an output layer, so it consists of a single final gate fed by a selected set of first-layer gates (`FABL.CircuitTail.eq_output_of_layerCount_eq_one`). Consequently the circuit computes the function obtained by applying that final gate to those first-layer outputs. The depth-two representation result for such a final gate says that this function has either a DNF or a CNF representation of width at most the circuit's width (`FABL.DepthCircuit.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE`).

**Key facts.** `FABL.CircuitTail.eq_output_of_layerCount_eq_one`, `FABL.DepthCircuit.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE`.
