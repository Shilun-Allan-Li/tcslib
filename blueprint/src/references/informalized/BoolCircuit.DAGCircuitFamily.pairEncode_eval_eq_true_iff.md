<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuitFamily.pairEncode_eval_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation on paired inputs

**Claim.** The circuit in the family for inputs of length $2n+2+|r|$, evaluated on the input formed by duplicating each bit of $v$ and appending $01$ and $r$, outputs $1$ exactly when the paired encoding of $v$ and $r$ belongs to the language accepted by the family.

**Proof.** Apply the characterization of language membership for a list obtained from a Boolean vector: membership is equivalent to the family circuit on that vector outputting $1$ (`mem_language_ofFn`). Use the equality identifying the list of bits in the paired input with the paired encoding of $v$ and $r$ (`pairEncodeInput_ofFn`). Replacing the list by this equal list in the membership statement gives the claimed equivalence.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_ofFn`, `BoolCircuit.pairEncodeInput_ofFn`.
