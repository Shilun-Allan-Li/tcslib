<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.emitNots_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Negation-Gate Emission

**Claim.** Given an acyclic gate list $G$ and valid input vertices $a_1,\ldots,a_m$, emitting one negation gate for each listed vertex extends $G$ by $m$ gates and returns distinct valid output indices whose values are the corresponding negations. The extended list remains acyclic, the outputs satisfy the stated depth bound, and every appended gate is well formed and is a negation gate.

**Proof.** Proceed by induction on the list of vertices. For the empty list, the procedure returns the original gates and no output indices, so the required properties reduce to those already assumed or to empty-list facts.

For the inductive step, let $a$ be the first vertex. Append the gate that negates $a$, and call the resulting list $G'$. The bound on $a$ makes this new gate read an earlier vertex, so appending it preserves acyclicity (`BoolCircuit.GatesAcyclic.snoc`). Every remaining listed vertex is still valid in $G'$, because its old bound is below the new input range. Apply the induction hypothesis to the remaining list and $G'$.

The returned list is the new gate followed by the induction hypothesis's extension; the outputs are the index of the newly appended gate followed by the remaining outputs. The new index is strictly beyond the old circuit's vertex range and below the final range. The induction hypothesis supplies the same bounds for the other outputs, and their lower bounds also show that none equals the new index, proving distinctness. The extension and length claims follow by joining the one new gate to the inductive extension.

For values, the new gate's value is the negation of the old value at $a$, by the fact that appending gates does not change earlier vertex values and that the value of the last gate is its evaluation on the preceding circuit (`BoolCircuit.vertexValue_append`, `BoolCircuit.vertexValue_last`). The induction hypothesis gives the values for the remaining outputs. Their source vertices are all old vertices, so their values are unchanged by the added gate.

For depths, the new output has depth one plus the depth at $a$, by the corresponding append and last-gate depth facts (`BoolCircuit.vertexDepth_append`, `BoolCircuit.vertexDepth_last`). The depth at $a$ is bounded by the maximum over the listed vertices (`BoolCircuit.le_foldr_max₂`), yielding the claimed bound. Each remaining output retains its depth from the inductive construction; the maximum of their source depths in the enlarged circuit is bounded by the original maximum, using preservation of old depths and the fact that each listed depth is at most the list maximum (`BoolCircuit.vertexDepth_append`, `BoolCircuit.le_foldr_max₂`, `BoolCircuit.foldr_max_le₂`). Finally, the dropped suffix consists of the new singleton negation gate followed by the inductive suffix, so every appended gate has the asserted form and well-formedness.

**Key facts.** `BoolCircuit.GatesAcyclic.snoc`, `BoolCircuit.vertexValue_append`, `BoolCircuit.vertexValue_last`, `BoolCircuit.vertexDepth_append`, `BoolCircuit.vertexDepth_last`, `BoolCircuit.le_foldr_max₂`, `BoolCircuit.foldr_max_le₂`.
