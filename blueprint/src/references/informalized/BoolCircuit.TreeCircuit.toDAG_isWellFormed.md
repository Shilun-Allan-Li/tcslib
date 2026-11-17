<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.toDAG_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formed Compiled Circuits

**Claim.** Every gate in the compiled directed acyclic circuit of a Boolean circuit tree has no repeated input vertices, and each NOT gate has exactly one input.

**Proof.** Compile the tree starting from the empty gate list, which is acyclic (`BoolCircuit.GatesAcyclic.nil`). The compilation specification (`BoolCircuit.compileTree_spec`) ensures that every gate newly produced by the compilation has no repeated inputs and satisfies the required input-count condition for NOT gates. The gates of the compiled circuit are precisely these newly produced gates, so each has both properties.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_spec`.
