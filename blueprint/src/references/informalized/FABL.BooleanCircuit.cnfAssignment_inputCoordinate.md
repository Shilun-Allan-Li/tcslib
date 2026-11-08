<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.cnfAssignment_inputCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input coordinates of the assignment

**Claim.** At the coordinate corresponding to input position $i$, the extended sign assignment associated with an input $x$ equals the sign corresponding to the bit $x(i)$.

**Proof.** By definition, the extended assignment uses the input assignment on the first $n$ coordinates and the gate values on the remaining coordinates. The input coordinate is the image of $i$ under the inclusion of the first block, so evaluating the extension there returns the sign assigned to $x(i)$.
