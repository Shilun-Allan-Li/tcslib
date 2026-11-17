<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.length_progGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate count and program offset

**Claim.** For each $i\le |prog|$, the number of input vertices plus the number of gates generated from the first $i$ instructions equals the base vertex index assigned to stage $i$.

**Proof.** We induct on the stage $i$. At stage zero, the program gate list consists of the two constant gates; substituting this initial list and the definition of the base index gives the equality. For the successor stage, the construction appends the embedded gates for the instruction at index $i$. The length of those appended gates is the embedded width of that instruction's kind gadgets (`length_embedAll`). By the induction hypothesis, the previous gate count plus the number of input vertices is the previous base index. The base-index definition adds the width of the next instruction's gadgets, and the hypothesis $i+1\le |prog|$ ensures that the instruction at index $i$ is present. These expressions agree, yielding the successor equality.

**Key facts.** `BoolCircuit.length_embedAll`.
