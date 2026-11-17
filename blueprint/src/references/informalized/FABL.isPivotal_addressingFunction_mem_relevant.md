<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.isPivotal_addressingFunction_mem_relevant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotal coordinates of the addressing function

**Claim.** If changing coordinate $i$ changes the addressing function’s output, then $i$ is either an address coordinate or the data coordinate selected by the input’s address.

**Proof.** The coordinate $i$ belongs to exactly one of the two parts in the decomposition of the coordinates into address and data coordinates. If it is an address coordinate, it belongs to the set of all address coordinates, hence to the relevant-coordinate set. Otherwise write it as the data coordinate indexed by $j$. If $j$ is the index selected by the input’s address, then this coordinate is included as the selected data coordinate. If it is not selected, flipping that data coordinate leaves the addressing function’s output unchanged (`FABL.addressingFunction_flip_data_of_ne`). This contradicts the assumed pivotality, so the data coordinate must be the selected one.

**Key facts.** `FABL.addressingFunction_flip_data_of_ne`.
