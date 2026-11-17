<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.gatesAcyclic_embedAll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of successive circuit embeddings

**Claim.** Given circuits $D_1,\ldots,D_r$ with $m$ input vertices and a length-$m$ source list whose entries are below $L$, the list formed by embedding them successively, advancing the offset by each gate count plus one, is acyclic from $L$.

**Proof.** Induct on the list of circuits, allowing the starting offset to vary. For the empty list, acyclicity holds because there are no gates (\texttt{GatesAcyclic.nil}). For a nonempty list with first circuit $D$, the embedded gates of $D$ are acyclic from the current offset, and the induction hypothesis makes the embeddings of the remaining circuits acyclic from the offset advanced by $|D.\mathrm{gates}|+1$. The concatenation is therefore acyclic by the concatenation theorem for acyclic lists (\texttt{GatesAcyclic.append}). The source indices remain below the advanced offset because they were below $L$ and the offset only increases.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.gatesAcyclic_embedGates`, `BoolCircuit.GatesAcyclic.append`.
