<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.gatesAcyclic_progGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of program gates

**Claim.** For a program of length $|\mathrm{prog}|$, the gates produced for its first $i$ stages are acyclic from the input bound $n$ whenever $i\le |\mathrm{prog}|$.

**Proof.** Use induction on the number $i$ of stages. At zero stages the list consists of the two constant gates; their argument lists are empty, so the list is acyclic. For the successor step, the induction hypothesis gives acyclicity of the gates already produced. The gates for the next stage are an embedding of the circuits for that instruction, using its source vertices and the offset just beyond the existing gates. The source list has length $m$ and all its entries are below that offset, so the embedded list is acyclic from the offset by \texttt{gatesAcyclic_embedAll}. The length identity \texttt{length_progGates} identifies this offset with $n$ plus the length of the existing gate list. The two acyclic lists can therefore be concatenated using \texttt{GatesAcyclic.append}.

**Key facts.** `BoolCircuit.GatesAcyclic.append`, `BoolCircuit.gatesAcyclic_embedAll`, `BoolCircuit.length_progGates`, `BoolCircuit.length_srcVertices`, `BoolCircuit.srcVertices_lt`.
