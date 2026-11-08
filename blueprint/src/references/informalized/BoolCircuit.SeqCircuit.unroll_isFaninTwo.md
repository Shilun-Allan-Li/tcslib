<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In of the Unrolled Circuit

**Claim.** If the combinational circuit is well formed and every one of its gates has at most two inputs, then its unrolling has distinct inputs at each gate, exactly one input at each NOT gate, and at most two inputs at each gate.

**Proof.** The unrolling is well formed by `unroll_isWellFormed`, so it already has distinct inputs at each gate and exactly one input at each NOT gate. It remains to bound the number of inputs. Any gate in the unrolled gate list comes from some position $p$. By `unrollGate_cases`, it either has at most one input, which suffices, or is a combinational gate with its arguments mapped through the placement function. In the latter case, mapping preserves the argument-list length, so the original gate's at-most-two-input bound gives the desired bound.

**Key facts.** `BoolCircuit.SeqCircuit.unroll_isWellFormed`, `BoolCircuit.SeqCircuit.unrollGate_cases`.
