<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: Language.InTreeSize.inSIZE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree-to-circuit size bound

**Claim.** If every input length $n$ has a tree of size at most $T(n)$ recognizing the length-$n$ words of a language, then that language has well-formed acyclic fan-in-two circuits recognizing it, with size at most $n+3T(n)$.

**Proof.** Start with the tree assigned to each input length. First convert it to a binary tree, which preserves evaluation, has fan-in at most two, and has size at most three times the original tree size. Then convert that binary tree to a directed acyclic circuit. This circuit is well formed, has fan-in at most two, and has size at most the input length plus the binary tree's size. Consequently its size is at most $n+3T(n)$. The two evaluation-preservation results show that on every Boolean input the circuit accepts exactly when the original tree does, so the resulting circuit family recognizes the given language.

**Key facts.** `BoolCircuit.toBinary_maxFanin_le`, `BoolCircuit.toBinary_size_le`, `BoolCircuit.TreeCircuit.toDAG_isFaninTwo`, `BoolCircuit.TreeCircuit.toDAG_size_le`, `BoolCircuit.toBinary_eval`, `BoolCircuit.TreeCircuit.toDAG_eval`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
