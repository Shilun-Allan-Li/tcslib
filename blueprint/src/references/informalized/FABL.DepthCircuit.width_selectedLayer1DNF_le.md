<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.width_selectedLayer1DNF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of Selected First-Layer Terms

**Claim.** For any finite set of indices of the first-layer gates of a depth circuit, the width of the DNF consisting of the selected gates is at most the width of the circuit.

**Proof.** By the characterization of DNF width, it suffices to show that every term in the selected DNF has width at most the circuit's width. A term in the selected DNF is the gate at some selected index. That gate occurs in the circuit's full first layer, so its width is at most the width of the DNF formed from that full layer. This proves the required bound for every selected term, and hence for the selected DNF.

**Key facts.** `FABL.DNFFormula.width_le_iff`, `FABL.DNFFormula.width_le_of_mem`.
