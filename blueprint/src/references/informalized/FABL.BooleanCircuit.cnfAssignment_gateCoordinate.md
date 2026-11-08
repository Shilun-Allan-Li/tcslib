<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.cnfAssignment_gateCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF assignment at a gate

**Claim.** At the coordinate for gate $i$, the extended sign assignment associated with input $x$ equals the sign corresponding to the Boolean value of gate $i$ on $x$.

**Proof.** The gate coordinate places $i$ in the auxiliary, gate-indexed part of the extended assignment. The circuit’s CNF assignment uses the sign of the evaluated gate as the value at each such auxiliary coordinate. Evaluating at the coordinate for $i$ thus gives the sign of the value of gate $i$ on $x$.
