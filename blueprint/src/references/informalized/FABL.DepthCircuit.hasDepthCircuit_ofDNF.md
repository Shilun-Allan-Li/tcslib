<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.hasDepthCircuit_ofDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit representation of a DNF

**Claim.** Every DNF formula is computed by a depth-two layered circuit whose size is the number of terms and whose first-layer width is the maximum width of its terms.

**Proof.** Represent the DNF formula by its associated layered circuit. The circuit representation theorem supplies a representation of the function computed by that circuit, with the circuit's depth, size, and width. The construction-specific facts identify these parameters as depth two, the number of DNF terms, and the maximum term width, respectively; they also identify the computed function with the original formula. Substituting these facts yields the claimed representation.

**Key facts.** `FABL.DepthCircuit.hasDepthCircuit_toBooleanFunction`, `FABL.DepthCircuit.depth_ofDNF`, `FABL.DepthCircuit.size_ofDNF`, `FABL.DepthCircuit.width_ofDNF`, `FABL.DepthCircuit.toBooleanFunction_ofDNF`.
