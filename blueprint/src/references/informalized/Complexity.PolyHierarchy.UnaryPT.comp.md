<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.UnaryPT.comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of unary polynomial-time functions

**Claim.** If the unary word function associated to $\ell$ is polynomial-time computable and $f$ is polynomial-time computable, then the unary word function associated to $y\mapsto\ell(f(y))$ is polynomial-time computable.

**Proof.** The unary word function for the composite is exactly the composition of the unary word function for $\ell$ with $f$: on input $y$, it produces $1^{\ell(f(y))}$. The closure of polynomial-time computable functions under composition (`Complexity.PolyTimeComputable.comp`) therefore gives polynomial-time computability of this function, which is the defining condition for the claimed unary property.

**Key facts.** `Complexity.PolyTimeComputable.comp`.
