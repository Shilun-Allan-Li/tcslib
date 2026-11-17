<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CircuitThreeCNFPolytimeAdapter.promiseKarpReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-to-three-CNF promise reduction

**Claim.** The certified polynomial-time map gives a Karp reduction from circuit satisfiability to three-CNF satisfiability, preserving both promised yes instances and promised no instances.

**Proof.** Use the adapter’s certified polynomial-time map as the reduction. To verify preservation of yes instances, take an input in the source yes set and split according to whether it decodes as a circuit. A malformed input cannot belong to that set. For a decoded circuit, the encoding is canonical, so the adapter’s behavior on canonical encodings and the target encoding’s decode-after-encode law show that the output decodes as the circuit’s associated three-CNF formula. The circuit-to-formula satisfiability equivalence ( `satisfiable_iff_toExactlyThreeCNF_satisfiable`) then gives a target yes instance. For a source no instance, the malformed case is again impossible. In the decoded case the same canonical-output argument applies; if the resulting formula were satisfiable, the reverse direction of that equivalence would make the circuit satisfiable, contradicting that the input is a source no instance. Thus the map preserves both sides of the promise.

**Key facts.** `FABL.BooleanCircuit.satisfiable_iff_toExactlyThreeCNF_satisfiable`.
