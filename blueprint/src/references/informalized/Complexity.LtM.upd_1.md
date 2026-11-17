<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.LtM.upd_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Second Coordinate

**Claim.** Updating the function with values $a$ and $b$ at indices $0$ and $1$ at index $1$ to value $c$ gives the function with values $a$ and $c$.

**Proof.** There are only two indices. At index $0$, the update leaves the original value unchanged, namely $a$. At index $1$, it replaces the value by $c$. Hence the updated function has the stated values at both indices.
