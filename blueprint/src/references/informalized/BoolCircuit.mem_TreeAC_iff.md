<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.mem_TreeAC_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in Tree AC

**Claim.** A Boolean language belongs to the union of the tree-circuit classes over all natural-number depth exponents exactly when, for some natural number $i$, it has a polynomial-size tree-circuit family recognizing the language with depth bounded by a polynomial in $\log n+1$ of degree $i$.

**Proof.** Unfold the union defining $\mathrm{TreeAC}$. A language belongs to it exactly when it belongs to $\mathrm{TreeACLevel}(i)$ for some natural number $i$. By the definition of that level, this is exactly $L\in\mathrm{InTreeAC}(i)$, yielding the asserted characterization.
