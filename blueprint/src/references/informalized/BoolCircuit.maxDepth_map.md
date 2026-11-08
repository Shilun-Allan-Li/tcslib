<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.maxDepth_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a mapped list of circuits

**Claim.** The maximum depth of the circuits obtained by applying $f$ to a list equals the fold taking the maximum of their individual depths, with value $0$ for the empty list.

**Proof.** Induct on the list. For the empty list, both expressions are $0$. For a list with head $a$ and tail $\ell$, the maximum depth of the mapped list is the maximum of $\mathrm{depth}(f(a))$ and the maximum depth of the mapped tail, by the head-tail formula for maximum depth (`BoolCircuit.TreeCircuit.maxDepth_cons`). The induction hypothesis identifies the tail maximum with the fold of the tail’s depths; this is exactly the head-tail expansion of the stated fold.

**Key facts.** `BoolCircuit.TreeCircuit.maxDepth_cons`.
