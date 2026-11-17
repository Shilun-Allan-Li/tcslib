<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTab.lean :: Complexity.Meyer.init_tag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial input-head boundary tag

**Claim.** The initial input-head position has the true virtual boundary tag: its tag is false at position $0$ and true at the right boundary $|x|+1$.

**Proof.** The initial head position is $1$. It is therefore not $0$, so the implication required at the left boundary holds vacuously. The right-boundary implication is also vacuous: position $1$ equals $|x|+1$ only when $|x|=0$, and in that case the required tag is true. Hence both clauses of the virtual-tag condition hold.
