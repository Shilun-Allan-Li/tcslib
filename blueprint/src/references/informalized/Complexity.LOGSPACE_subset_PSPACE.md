<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LOGSPACE_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space Lies in Polynomial Space

**Claim.** Every binary language decidable using logarithmic work space belongs to polynomial space.

**Proof.** For each input length $n$, the logarithmic space bound satisfies $\mathrm{logSpace}(n)\le n+1$. By monotonicity of the space classes (`Complexity.SPACE.mono`), this gives $\mathrm{SPACE}(\mathrm{logSpace})\subseteq \mathrm{SPACE}(n\mapsto n+1)$. The latter is contained in PSPACE by the polynomial-space inclusion with exponent $1$ (`Complexity.space_poly_subset_PSPACE`). Since $\mathrm{LOGSPACE}=\mathrm{SPACE}(\mathrm{logSpace})$, composing these inclusions proves the claim.

**Key facts.** `Complexity.SPACE.mono`, `Complexity.logSpace_le_succ`, `Complexity.space_poly_subset_PSPACE`.
