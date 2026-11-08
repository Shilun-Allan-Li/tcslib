<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.maxDepth_map_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for mapped circuits

**Claim.** If each circuit $c$ in a finite list satisfies $\mathrm{depth}(f(c))\le m$, then the maximum depth among the mapped circuits is at most $m$, including the empty-list convention.

**Proof.** Induct on the list. For the empty list, its maximum depth is $0\le m$. For a head $c$ and tail $cs$, the hypothesis gives $\mathrm{depth}(f(c))\le m$ and, by restriction, every member of $cs$ also satisfies the bound. The induction hypothesis bounds the maximum depth of the mapped tail by $m$. The maximum depth of the whole mapped list is the maximum of these two quantities (`BoolCircuit.TreeCircuit.maxDepth_cons`), and therefore is at most $m$.

**Key facts.** `BoolCircuit.TreeCircuit.maxDepth_cons`.
