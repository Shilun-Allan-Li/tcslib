<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.f₂DotProductBilin_isRefl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of orthogonality

**Claim.** For every $n$, the binary dot-product bilinear form is reflexive in the sense expressed by `IsRefl`.

**Proof.** The proof uses the fact that a symmetric bilinear form is reflexive in this orthogonality sense. Since the binary dot-product form is symmetric, this fact applies directly and gives the result. This does not assert that every vector has zero dot product with itself; that assertion would be false in general over $\mathbb{F}_2$.

**Key facts.** `FABL.f₂DotProductBilin_isSymm`.

**Caveat.** The supplied informal statement describes self-orthogonality, but the formal theorem and its proof establish reflexivity from symmetry. In general, binary vectors need not have zero dot product with themselves.
