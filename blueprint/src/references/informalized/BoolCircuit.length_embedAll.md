<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.length_embedAll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Combined Embedded Gates

**Claim.** For a finite list of directed acyclic circuits with $m$ input vertices, the combined list formed by embedding them successively has length equal to the sum of their widths, regardless of the source list and starting index.

**Proof.** Induct on the list of circuits, allowing the starting index $L$ to vary. For the empty list, both the combined gate list and the sum of widths have length zero. For a list with first circuit $D$ and remaining list $D_s$, the combined list is the embedded gates of $D$ appended to the combined list for $D_s$ at the next starting index. Its length is therefore the length of the first list plus the length of the remaining list. The embedded gates of $D$ consist of one remapped, deduplicated gate for each gate of $D$, followed by one additional gate, so their length is $|D.\mathrm{gates}|+1$. The induction hypothesis gives the remaining list length as the width of $D_s$; adding these lengths is exactly the recursive definition of the width of $D::D_s$.
