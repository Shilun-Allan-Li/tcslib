<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.size_ofCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Circuit Representing a CNF

**Claim.** The circuit formed from a CNF formula by taking its clauses as the first layer and adding a single output layer has size equal to the number of clauses.

**Proof.** In the constructed circuit, the first layer is exactly the list of clauses, so its number of gates is the number of clauses. The remaining tail is the output layer, which contributes no internal nodes. By the definition of circuit size as first-layer gates plus internal nodes in the tail, the circuit size is therefore exactly the clause count.
