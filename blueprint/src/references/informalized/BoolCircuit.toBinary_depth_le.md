<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.toBinary_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for binary conversion

**Claim.** If every gate of a circuit tree $c$ has fan-in at most $w$, then its binary conversion has depth at most $\mathrm{depth}(c)(\lceil\log_2 w\rceil+1)$.

**Proof.** Proceed by structural induction on $c$. A literal has depth zero, and its conversion has depth zero as well. For a node with children $cs$, the bound on the node’s maximum fan-in implies both that $|cs|\le w$ and that every child has maximum fan-in at most $w$ (by the node maximum-fan-in formula and the list maximum bound). The induction hypotheses therefore bound each converted child’s depth by its original depth times $\lceil\log_2 w\rceil+1$. Taking the maximum over the children preserves this bound; the depth of the converted-child list is thus at most the original children’s maximum depth times that factor. The binary-combination depth estimate (combine_depth) adds at most $\lceil\log_2 |cs|\rceil+1$ to that maximum. Monotonicity of the ceiling logarithm and $|cs|\le w$ bound this additive term by $\lceil\log_2 w\rceil+1$. The original node depth is one plus the maximum child depth, so adding these estimates gives the claimed product bound.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL`, `BoolCircuit.TreeCircuit.depth_le_maxDepth`, `BoolCircuit.combine_depth`.
