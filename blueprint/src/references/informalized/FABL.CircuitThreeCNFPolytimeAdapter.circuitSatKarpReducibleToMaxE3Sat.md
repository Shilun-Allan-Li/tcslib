<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CircuitThreeCNFPolytimeAdapter.circuitSatKarpReducibleToMaxE3Sat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability Karp Reduction

**Claim.** For an adapter providing a certified polynomial-time map with the stated encoding behavior, the language of satisfiable circuit encodings is Karp reducible to the language of satisfiable three-CNF encodings.

**Proof.** The adapter's Karp-reducibility theorem applies directly: its polynomial-time map is the reduction, and its encoding conditions ensure that an input is in the circuit language exactly when its image is in the three-CNF language.

**Key facts.** `FABL.CircuitThreeCNFPolytimeAdapter.karpReducible`.

**Caveat.** The payload's informal PCPP and Max-E3-Sat sketch does not describe this formal theorem or its proof; the proof source establishes the encoding-based Karp reduction.
