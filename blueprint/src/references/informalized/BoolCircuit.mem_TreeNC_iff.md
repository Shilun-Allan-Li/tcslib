<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.mem_TreeNC_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in Tree NC

**Claim.** A Boolean language belongs to the union of the tree-circuit classes with depth exponent at least one exactly when, for some integer $i\ge1$, it has a fan-in-two tree-circuit family recognizing the language, of polynomial size and depth bounded by a polynomial in $\log n+1$ of degree $i$.

**Proof.** Unfold the definition of $\mathrm{TreeNC}$ as a union over indices $i$ restricted to $\mathrm{Ici}(1)$. Membership in this union means that for some such $i$, the language belongs to $\mathrm{TreeNCLevel}(i)$. The restriction says $1\le i$, and membership in the level means precisely $L\in\mathrm{InTreeNC}(i)$. This gives the claimed equivalence.
