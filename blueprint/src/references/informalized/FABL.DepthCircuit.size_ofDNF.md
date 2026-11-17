<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.size_ofDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the DNF circuit

**Claim.** For every DNF formula, the size of the circuit obtained from it is the number of terms in the formula.

**Proof.** The circuit formed from the formula has its terms as its first layer, and its tail is the output layer. The size is the number of first-layer gates plus the number of internal nodes in the tail. The output layer contributes no internal nodes, so the size reduces to the length of the term list, which is exactly the formula's size.
