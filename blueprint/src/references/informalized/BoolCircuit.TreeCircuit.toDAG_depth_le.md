<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.toDAG_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for the DAG translation

**Claim.** For every Boolean circuit $c$ on $n$ variables, the depth of its directed acyclic graph translation is at most $\mathrm{depth}(c)+1$.

**Proof.** Start the compilation with no previously constructed gates, a list that is acyclic. The compilation specification (BoolCircuit.compileTree_spec) applies to this initial gate list and certifies the compiled circuit's properties, including its depth bound. Its depth conclusion is precisely that the depth of the DAG translation is at most the tree depth plus one.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_spec`.
