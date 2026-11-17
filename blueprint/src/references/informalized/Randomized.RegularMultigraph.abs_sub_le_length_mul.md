<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.abs_sub_le_length_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variation along a graph walk

**Claim.** If the values of $F$ differ by at most $a$ across each neighbor step, then along any walk from $x$ to $t$, the difference $|F(x)-F(t)|$ is at most the walk length times $a$.

**Proof.** Induct on the walk. For the walk of length zero, its endpoints coincide, so the claimed difference is zero. For a walk formed by first stepping from $x$ to $y$ and then following a shorter walk from $y$ to $t$, adjacency means that some neighbor slot goes from one endpoint to the other. The assumed bound therefore gives $|F(x)-F(y)|\le a$; if the slot is given in the reverse direction, use symmetry of absolute value. The induction hypothesis bounds $|F(y)-F(t)|$ by the length of the shorter walk times $a$. Since $F(x)-F(t)=(F(x)-F(y))+(F(y)-F(t))$, the triangle inequality bounds its absolute value by the sum of these two bounds. This sum is $a$ times one plus the shorter length, which is exactly the length of the original walk times $a$.
