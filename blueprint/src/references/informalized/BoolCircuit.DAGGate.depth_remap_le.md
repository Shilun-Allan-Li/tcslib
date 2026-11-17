<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGGate.depth_remap_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under remapping

**Claim.** If every argument of a Boolean circuit gate has remapped depth at most its original depth plus one, then the remapped gate’s depth is at most the original gate’s depth plus one.

**Proof.** The depth of a gate is one plus the maximum of the defaulted depths of its arguments, with the empty maximum taken to be zero. Apply the bound on each argument to the two lists of depths: the maximum of the remapped values is at most the maximum of the original values plus one (`foldr_max_le_succ`). Adding the initial one in the definition of depth gives the claimed inequality.

**Key facts.** `BoolCircuit.foldr_max_le_succ`.
