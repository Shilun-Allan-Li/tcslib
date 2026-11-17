<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_majorityThree_skeleton_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement of a sign-dependent coordinate choice

**Claim.** For a uniform sign vector on the three-dimensional cube and a choice of coordinate $j$ that always differs from the fixed coordinate $i$, the probability that the sign at $j(x_i)$ differs from $x_i$ is $1/2$.

**Proof.** Express the uniform expectation as the sum of the indicator over all sign vectors divided by the cube's cardinality. Reparameterize the three coordinates as the independent pair of signs and the remaining sign, then fix the two values $j(1)$ and $j(-1)$. Enumerating the possible fixed coordinate and these two choices, subject to each choice differing from the fixed coordinate, gives the stated fraction of disagreements, namely $1/2$.
