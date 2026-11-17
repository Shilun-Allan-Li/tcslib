<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.pairEncode_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under pair encoding

**Claim.** For every assignment to the $n$ inputs, evaluating the circuit obtained by wiring its inputs according to the pair encoding gives the same output as evaluating the original circuit on the encoded input.

**Proof.** By the input-buffer evaluation theorem (`DAGCircuit.bufferInputs_eval`), the evaluation of the circuit after wiring by `pairWiring n r` equals the evaluation of $C$ on the assignment obtained by reading each wire as either an input bit or a constant. By definition, this assignment is `pairEncodeInput r v`. Substituting this identity gives the claimed equality.

**Key facts.** `BoolCircuit.DAGCircuit.bufferInputs_eval`.
