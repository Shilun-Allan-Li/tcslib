<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.LtM.upd_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First Coordinate

**Claim.** Updating the function with values $a$ and $b$ at indices $0$ and $1$ at index $0$ to value $c$ gives the function with values $c$ and $b$.

**Proof.** There are only two indices. At index $0$, the update replaces the value by $c$. At index $1$, the update leaves the original value unchanged, namely $b$. These pointwise equalities establish equality of the two functions.
