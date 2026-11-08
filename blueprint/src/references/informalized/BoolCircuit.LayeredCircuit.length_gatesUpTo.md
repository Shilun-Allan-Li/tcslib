<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.length_gatesUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Gate Prefix

**Claim.** For every natural number $m$, the list of gates through the first $m$ layers has length equal to the sum, over $j<m$, of the numbers of nodes in layer $j+1$ when $j<\mathrm{depth}(F)$, with each summand zero otherwise.

**Proof.** Proceed by induction on $m$. At zero, both the gate list and the offset sum are empty, so their lengths agree. At a successor, the gate list is the previous prefix followed by the gates for layer $m+1$ when $m$ is below the depth, and followed by an empty list otherwise. Its length is thus the previous length plus the cardinality of that layer in the first case, or just the previous length in the second. The offset's successor formula (`offset_succ`) gives the same addition, and the definition of the layer cardinality (`succCard`) makes the two cases agree.

**Key facts.** `BoolCircuit.LayeredCircuit.offset_succ`.
