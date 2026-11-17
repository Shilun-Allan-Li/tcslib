<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.real_inner_probabilitySimplexEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Simplex Vertices

**Claim.** The inner product of the standard basis vectors associated with $a$ and $b$ is $1$ when $a=b$ and $0$ otherwise.

**Proof.** Write the inner product in coordinates. Its summand at $	au$ is nonzero only if both $	au=b$ and $	au=a$. If $a=b$, exactly the coordinate $	au=a$ contributes $1$, and all others contribute zero. If $a\ne b$, no coordinate satisfies both equalities, so every summand vanishes.
