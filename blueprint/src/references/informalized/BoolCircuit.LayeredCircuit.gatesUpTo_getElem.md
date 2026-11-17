<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.gatesUpTo_getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Position in the Bounded List

**Claim.** For a layer $m$ below the circuit depth and a node $u$ in its successor layer, the gate at the index given by the cumulative count of earlier successor-layer nodes plus the rank of $u$ is precisely the gate associated with $u$.

**Proof.** The list through layer $m+1$ is the list through layer $m$ followed by the gates for layer $m$. The length of the earlier list is $\mathrm{offset}(m)$, so the stated index, which adds the rank of $u$, selects position $(\mathrm{layerEnum}(u)).\mathrm{val}$ within the appended portion. That portion is enumerated by applying the layer-gate construction to the inverse enumeration of the layer's nodes. At the indicated rank, the inverse enumeration returns $u$, so the selected gate is exactly the gate associated with $u$.

**Key facts.** `BoolCircuit.LayeredCircuit.length_gatesUpTo`.
