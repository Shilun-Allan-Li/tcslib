<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-layer gate width bound

**Claim.** For any set of first-layer gates feeding a second-layer gate, its computed function has either a DNF or a CNF representation of width at most the circuit width.

**Proof.** Split according to the first-layer gate type. When those gates are AND gates, the selected first-layer terms form a DNF for the second-layer function; the supplied width bound shows this DNF has width at most the circuit width (`width_selectedLayer1DNF_le`), and the evaluation identity identifies its function with the second-layer gate function (`selectedLayer1DNF_toBooleanFunction`). When the first-layer gates are OR gates, the selected terms instead form a CNF; its width is bounded in the same way (`width_selectedLayer1CNF_le`), and its evaluation gives the second-layer function (`selectedLayer1CNF_toBooleanFunction`). Thus one of the two representations always exists.

**Key facts.** `FABL.DepthCircuit.width_selectedLayer1DNF_le`, `FABL.DepthCircuit.selectedLayer1DNF_toBooleanFunction`, `FABL.DepthCircuit.width_selectedLayer1CNF_le`, `FABL.DepthCircuit.selectedLayer1CNF_toBooleanFunction`.
