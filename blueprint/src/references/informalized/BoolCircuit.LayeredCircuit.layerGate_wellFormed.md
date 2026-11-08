<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.layerGate_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formed Layer Gates

**Claim.** For every layer $m$ below the depth of $F$ and every node $u$ in its successor, the associated gate has pairwise distinct argument vertices, and if its kind is NOT then it has exactly one argument.

**Proof.** Unfold the associated gate's definition and consider its three shapes. For a wire, the gate has AND kind and a singleton argument list, which is duplicate-free; the implication concerning NOT has a false premise. For a negation, the gate has NOT kind and a singleton argument list, so both required properties hold. For a conjunction, the gate has AND kind and its argument list is obtained by deduplicating the mapped input list, which is duplicate-free; again the NOT condition is vacuous.
