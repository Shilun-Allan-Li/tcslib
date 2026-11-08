<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of fan-in two

**Claim.** If $C$ has distinct arguments at every gate, exactly one argument at each NOT gate, and at most two arguments at each gate, then hardwiring the first $m$ inputs preserves all three properties.

**Proof.** The proof first obtains distinct arguments and the required NOT-gate arity from preservation of well-formedness (`hardwireLeft_isWellFormed`). It then considers any gate in the new circuit. A gate from the newly prepended constant gates has no arguments, so it has at most two. Any other gate is a remapped original gate: remapping changes only its argument labels, not the number of arguments, so the original bound of two applies. Together these give all the defining properties of fan-in two.

**Key facts.** `BoolCircuit.DAGCircuit.hardwireLeft_isWellFormed`.
