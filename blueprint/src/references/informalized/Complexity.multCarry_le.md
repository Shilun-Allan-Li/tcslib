<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multCarry_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Multiplication Carry

**Claim.** For bit strings $a,b$ and $j\in\mathbb{N}$, the carry into column $j$ in the multiplication procedure is at most the length of $a$.

**Proof.** Proceed by induction on the column index. The carry into column $0$ is zero, so the bound holds. For the step, suppose the carry into column $j$ is at most the length of $a$. The column contribution is also at most that length (`Complexity.multColumn_le`). Thus their sum is at most twice the length of $a$, and dividing by $2$ and taking the natural-number quotient shows that the carry into column $j+1$ is at most the length of $a$.

**Key facts.** `Complexity.multColumn_le`.
