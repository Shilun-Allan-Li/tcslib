<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean :: Complexity.space_poly_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial space inclusion

**Claim.** For every natural number $c$, every language in $\mathrm{SPACE}(n^c+1)$ belongs to $\mathrm{PSPACE}$.

**Proof.** By definition, $\mathrm{PSPACE}$ is the union over all exponents $d\in\mathbb N$ of $\mathrm{SPACE}(n^d+1)$. The class in the claim is exactly the term of this union indexed by $d=c$, and every term is contained in the union.
