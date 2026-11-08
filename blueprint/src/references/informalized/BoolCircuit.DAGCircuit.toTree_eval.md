<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.toTree_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the unfolded circuit

**Claim.** For every Boolean assignment, the tree obtained by unfolding a well-formed DAG circuit computes the same value as the DAG circuit.

**Proof.** Unfolding the circuit at its output vertex with fuel one greater than the output index and positive polarity gives a tree whose evaluation, by `BoolCircuit.DAGCircuit.unfoldVertex_eval`, is the value of that vertex in the circuit's computed value list. The output index is valid, so the lemma applies. The unfolded tree is exactly the tree used to define the circuit's unfolding, and the circuit's evaluation is exactly that value-list entry. Therefore the two evaluations agree.

**Key facts.** `BoolCircuit.DAGCircuit.unfoldVertex_eval`.
