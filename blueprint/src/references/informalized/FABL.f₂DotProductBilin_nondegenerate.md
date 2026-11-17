<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.f₂DotProductBilin_nondegenerate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondegeneracy of the binary dot product

**Claim.** For every $n$, the coordinate dot-product bilinear form on $\mathbb{F}_2^n$ is nondegenerate.

**Proof.** It is enough to show that the only vector orthogonal to every vector is zero. Suppose $x$ is orthogonal to every $y$. Then the linear functional given by pairing with $x$ is the zero functional, just as the functional given by pairing with the zero vector is. The dot-product equivalence between vectors and linear functionals is injective, so $x=0$. Thus the form is nondegenerate.
