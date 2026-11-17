<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of well-formedness

**Claim.** If every gate of $C$ has distinct arguments and each NOT gate has exactly one argument, hardwiring the first $m$ inputs preserves these properties.

**Proof.** A gate in the hardwired circuit is either a newly inserted constant gate or a remapped gate from $C$. Each constant gate has an empty argument list, hence distinct arguments, and is not a NOT gate (`constGate_kind_ne_not`). For a remapped original gate, its argument list is obtained by applying `leftPerm` to the original argument list. Since `leftPerm` is injective (`leftPerm_injective`), distinct original arguments remain distinct. The remapping leaves the gate kind and argument-list length unchanged, so any NOT gate still has exactly one argument.

**Key facts.** `BoolCircuit.constGate_kind_ne_not`, `BoolCircuit.DAGCircuit.leftPerm_injective`.
