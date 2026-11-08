<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CircuitThreeCNFPolytimeAdapter.karpReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability Reduces to Three-CNF

**Claim.** A certified polynomial-time map that correctly encodes each circuit's associated three-CNF formula and sends malformed circuit encodings to malformed formula encodings gives a Karp reduction from encoded circuit satisfiability to encoded three-CNF satisfiability.

**Proof.** Use the adapter's map as the reduction and verify membership equivalence for an arbitrary binary string. If the string does not decode to a circuit, the malformed-input condition says its image does not decode to a formula either, so both language-membership statements are false. If it decodes to a circuit, the encoding's canonicality property identifies the original string with that circuit's canonical encoding. The map's behavior on canonical encodings, followed by the target encoding's decode-after-encode property, shows that the image decodes to the associated three-CNF formula. Membership equivalence now reduces to the fact that a circuit is satisfiable exactly when its associated three-CNF formula is satisfiable (FABL.BooleanCircuit.satisfiable_iff_toExactlyThreeCNF_satisfiable). Thus the map preserves and reflects membership, as required for a Karp reduction.

**Key facts.** `FABL.BooleanCircuit.satisfiable_iff_toExactlyThreeCNF_satisfiable`.
