<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.layerVertex_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Vertex Values Match Circuit Evaluation

**Claim.** For every layer $m<\mathrm{depth}(F)+1$ and every node $u$ in that layer, evaluating the gate list through layer $m$ at the index assigned to $u$ gives the same Boolean value as evaluating the layered circuit at $u$ on the input assignment $x$.

**Proof.** Proceed by induction on the layer. In layer zero, the node is an input: `evalNode_zero` identifies its circuit value with the corresponding input value, while the assigned index is that input's index. The gate list through layer zero is empty, so `vertexValue_input` shows that reading this index returns the same input bit.

For the successor step, write the node's enumeration index as $j$. The gate evaluation equation `evalNode_succ`, together with the representation of a standard gate by its shape (`gateShape_spec`), expresses the node's value as the evaluation of its wire, negation, or conjunction shape on the previous layer's node values. The length formula for the prefix (`length_gatesUpTo`) and the offset successor formula (`offset_succ`) show that the gate for this node occurs at position $\mathrm{offset}(m)+j$ in the extended gate list. The indexed-gate fact (`gatesUpTo_getElem`) identifies that gate with the gate associated to $u$, and its assigned vertex index is $n+(\mathrm{offset}(m)+j)$.

Running the gate list reads each argument from the list of values already produced. Every argument of this gate lies below $n+\mathrm{offset}(m)$ (`layerGate_args_lt`), so its value is unchanged if the run is truncated just before the current gate. By monotonicity of the gate prefixes (`gatesUpTo_mono`), the shorter prefix through layer $m$ is an initial segment of this truncated list. The value at each such argument is therefore exactly the value assigned by `vertexValue` using the layer-$m$ prefix (`vertexValue_append`). Applying the induction hypothesis identifies these argument values with the corresponding layer-$m$ circuit values.

The gate's output consequently agrees with the original gate applied to those previous-layer values (`DAGGate.eval_congr`). In the wire case this is precisely the induction hypothesis for its source. In the negation case, the Boolean NOT conversion identity (`b2f_not`) turns Boolean negation into $1$ minus the encoded bit. In the conjunction case, deduplicating the inputs does not change their Boolean conjunction (`all_dedup'`); converting a Boolean list conjunction to the product of its encoded bits (`b2f_all`) then gives the conjunction shape's evaluation, using the induction hypothesis for each input. These three cases establish the successor step.

**Key facts.** `BoolCircuit.LayeredCircuit.evalNode_zero`, `BoolCircuit.vertexValue_input`, `BoolCircuit.LayeredCircuit.evalNode_succ`, `BoolCircuit.gateShape_spec`, `BoolCircuit.LayeredCircuit.length_gatesUpTo`, `BoolCircuit.LayeredCircuit.offset_succ`, `BoolCircuit.LayeredCircuit.gatesUpTo_getElem`, `BoolCircuit.LayeredCircuit.layerGate_args_lt`, `BoolCircuit.LayeredCircuit.gatesUpTo_mono`, `BoolCircuit.vertexValue_append`, `BoolCircuit.DAGGate.eval_congr`, `BoolCircuit.b2f_not`, `BoolCircuit.all_dedup'`, `BoolCircuit.b2f_all`.
