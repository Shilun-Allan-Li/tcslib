<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGGate.eval_tseitin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tseitin Encoding Characterizes Gate Evaluation

**Claim.** For a gate with at most two inputs, its Tseitin encoding at output index $z$ is satisfied by an assignment exactly when that assignment's value at $z$ equals the gate's evaluation on the given Boolean list.

**Proof.** Write the gate as its kind and argument list, and split according to whether the list has zero, one, or two entries. For no inputs, the encoding is a single unit clause fixing the output to the constant prescribed by that kind's evaluation; checking the two possible output values proves the equivalence. For one input $j$, the hypothesis identifies the list value at $j$ with the assigned value at $j$. Substituting this into the gate evaluation and checking the two possible values of the output and input verifies that the displayed clauses are satisfied exactly when the output equals the gate value. For two inputs $j,l$, obtain the same identifications for both inputs. For each gate kind, checking the eight possible triples of input and output values shows that the listed clauses hold exactly when the output agrees with the evaluation. Any longer argument list contradicts the assumed length bound, so there is no further case.
