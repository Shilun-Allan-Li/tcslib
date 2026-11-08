<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.hasDepthCircuit_ofCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit representation of a CNF

**Claim.** Every CNF formula has a depth-two circuit representation computing the same Boolean function, with size equal to the formula's size and first-layer width equal to its width.

**Proof.** Represent the CNF formula by its associated layered circuit. The circuit representation theorem says that this circuit computes its represented Boolean function and has a circuit representation with its own depth, size, and width. The construction-specific facts identify its depth as two, its size with the number of clauses, its width with the formula's width, and its computed function with the CNF formula. Substituting these equalities into the representation theorem gives the desired bounds and function equality.

**Key facts.** `FABL.DepthCircuit.hasDepthCircuit_toBooleanFunction`, `FABL.DepthCircuit.depth_ofCNF`, `FABL.DepthCircuit.size_ofCNF`, `FABL.DepthCircuit.width_ofCNF`, `FABL.DepthCircuit.toBooleanFunction_ofCNF`.
