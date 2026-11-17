<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.emitTrees_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness and Size Bound for Tree Emission

**Claim.** Emitting a tree for each list of valid vertices returns an acyclic extension and one valid output per list, with the corresponding gate values. The total length is bounded by the original length plus the sum of the individual tree costs, and every appended gate has the required kind, distinct inputs, and at most two inputs.

**Proof.** Induct on the list of vertex lists. The empty list leaves the circuit unchanged and returns no outputs, so the claims follow immediately. For a nonempty list with first member $vs$, first apply the single-tree result to $vs$ and the original circuit. Then apply the induction hypothesis to the remaining lists and the circuit produced by that first emission; the original vertex bounds remain valid because the first result extends the circuit. The recursive results therefore provide an acyclic final circuit, and their extensions concatenate to an extension of the original circuit.

The outputs consist of the first tree's root followed by the recursively produced roots. The first root remains valid after the later gates are appended, since earlier vertex values and indices are preserved (`BoolCircuit.vertexValue_append`); the other roots satisfy the recursive bounds. For each later output, its gate evaluation agrees with the one on the original circuit: the recursive value property applies, and each original input vertex retains its value through the first extension. This preservation follows by decomposing execution over concatenated gate lists and observing that a vertex below the initial value-list length is unchanged by running additional gates (`BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`). The output list length follows from the recursive length equality. The total size bound follows by adding the first tree's bound and the induction bound, matching the first cost plus the sum of the remaining costs. Finally, the appended suffix is the concatenation of the first emission's suffix and the later emission's suffix, so both recursive specifications establish the required properties of every new gate.

**Key facts.** `BoolCircuit.emitTree_spec`, `BoolCircuit.vertexValue_append`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`, `BoolCircuit.DAGGate.eval_congr`.
