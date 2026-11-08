<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Basic.lean :: Complexity.SPACE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of space classes

**Claim.** If $s_1(n)\le s_2(n)$ for every $n$, then every language decidable in space $s_1$ up to a constant factor is also decidable in space $s_2$ up to a constant factor.

**Proof.** Suppose $L$ is witnessed as belonging to $\mathrm{SPACE}(s_1)$ by a constant $c$ and a machine $M$. On inputs of length $n$, its space bound is $c\,s_1(n)$. The assumed pointwise inequality gives $c\,s_1(n)\le c\,s_2(n)$, so the same machine and constant witness membership in $\mathrm{SPACE}(s_2)$. The bound transfers by monotonicity of the machine's space requirement (`Turing.FinTM.ComputesInSpace.mono`).

**Key facts.** `Turing.FinTM.ComputesInSpace.mono`.
