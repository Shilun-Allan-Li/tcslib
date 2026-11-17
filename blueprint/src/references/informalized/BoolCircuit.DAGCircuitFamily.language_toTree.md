<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.DAGCircuitFamily.language_toTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language preserved by tree conversion

**Claim.** If every circuit in a Boolean DAG circuit family has distinct arguments at each gate and every NOT gate has exactly one argument, then unfolding the circuits into a tree family preserves the accepted language.

**Proof.** Fix an input word $w$. The tree-conversion evaluation theorem says that, under the stated well-formedness conditions, the converted tree circuit and the original DAG circuit have the same value on the assignment determined by $w$ (DAGCircuit.toTree_eval). Membership in each family's language is equivalent to that family's circuit on inputs of length $|w|$ evaluating to true (DAGCircuitFamily.mem_language_iff and TreeCircuitFamily.mem_language_iff). Thus $w$ is accepted by the converted tree exactly when it is accepted by the original family. Since this holds for every word, the two languages are equal.

**Key facts.** `BoolCircuit.DAGCircuit.toTree_eval`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `BoolCircuit.TreeCircuitFamily.mem_language_iff`.
