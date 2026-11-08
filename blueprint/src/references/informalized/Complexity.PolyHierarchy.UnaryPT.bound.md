<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.UnaryPT.bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound for unary outputs

**Claim.** If the unary representation of a function $\ell$ is polynomial-time computable, then $\ell(y)$ is bounded by a polynomial in the length of $y$, uniformly for all binary strings $y$.

**Proof.** Apply the polynomial output-length bound for polynomial-time computable functions (`Complexity.PolyTimeComputable.output_length_le`) to the function $y\mapsto 1^{\ell(y)}$. It supplies constants $A,a\in\mathbb N$ such that the length of this output is at most $A(|y|+1)^a$ for every $y$. Since the length of the unary word $1^{\ell(y)}$ is exactly $\ell(y)$, the same constants give the asserted bound.

**Key facts.** `Complexity.PolyTimeComputable.output_length_le`.
