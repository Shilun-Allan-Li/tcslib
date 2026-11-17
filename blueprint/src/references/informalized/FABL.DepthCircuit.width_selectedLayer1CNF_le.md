<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.width_selectedLayer1CNF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of Selected First-Layer Clauses

**Claim.** For any finite set of indices of the first-layer gates of a depth circuit, the width of the CNF formed from the selected gates is at most the width of the circuit.

**Proof.** The selected CNF stores exactly the terms obtained by selecting the given first-layer gates. Its width is therefore the width of the corresponding selected DNF. The result that selecting first-layer terms cannot increase width (`width_selectedLayer1DNF_le`) gives the desired inequality.

**Key facts.** `FABL.DepthCircuit.width_selectedLayer1DNF_le`.
