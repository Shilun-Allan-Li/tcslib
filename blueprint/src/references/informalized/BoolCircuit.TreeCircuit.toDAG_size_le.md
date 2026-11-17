<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.toDAG_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Circuit Size Bound

**Claim.** For a Boolean circuit tree on $n$ variables, the size of its compiled directed acyclic circuit is at most $n$ plus the number of nodes in the tree.

**Proof.** Compile the tree from the empty gate list, which is acyclic (`BoolCircuit.GatesAcyclic.nil`). The length bound in the compilation specification (`BoolCircuit.compileTree_spec`) bounds the number of gates added by the compilation by the tree's size. The size of the resulting directed acyclic circuit is $n$ plus its number of gates; substituting the compilation length bound gives the claimed inequality.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_spec`.
