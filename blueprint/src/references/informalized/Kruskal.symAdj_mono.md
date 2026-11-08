<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.symAdj_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of symmetric adjacency

**Claim.** If every edge in $e_1$ also occurs in $e_2$, then any two vertices symmetrically adjacent in $e_1$ are symmetrically adjacent in $e_2$.

**Proof.** Symmetric adjacency supplies an edge of $e_1$ with the given endpoints in one order or the other. The inclusion hypothesis places that same edge in $e_2$, with its endpoint equalities unchanged, which witnesses symmetric adjacency there.
