<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.deconst_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strictness of the transformed circuit

**Claim.** When $n>0$ and each original gate has distinct arguments, each NOT gate has one argument, and every gate has at most two arguments, every transformed gate has distinct arguments and has one argument if it is NOT and two otherwise.

**Proof.** A gate in the transformed circuit either belongs to the three-gate constant prefix or is the transformed image of an original gate. Each prefix gate is directly checked to have distinct arguments and the required arity: the NOT gate has one argument, while the OR and AND gates have two. For a transformed original gate, the original well-formedness and fan-in bounds say it has distinct arguments, has one argument when it is NOT, and has at most two arguments. The strict-gate lemma then gives distinct arguments and the required exact arity for its transformed image (`strictGate_strict`).

**Key facts.** `BoolCircuit.strictGate_strict`.
