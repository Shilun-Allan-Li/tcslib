<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.DAGCircuit.rewire_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size after rewiring

**Claim.** The rewired circuit has size $k+3+|G|$, where $G$ is the gate list of $C$.

**Proof.** The rewired circuit has $k$ inputs and a gate list consisting of two constant gates followed by the embedded gate list. The embedded list contains one remapped gate for each gate of $C$ and one additional output gate, so the total number of gates is $2+|G|+1$. Adding the $k$ inputs gives size $k+3+|G|$.
