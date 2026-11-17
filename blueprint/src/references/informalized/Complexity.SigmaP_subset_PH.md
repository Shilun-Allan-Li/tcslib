<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_subset_PH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Levels Lie in the Polynomial Hierarchy

**Claim.** For every natural number $i$, every language in $\Sigma_i^P$ belongs to $\mathsf{PH}=\bigcup_{r\in\mathbb{N}}\Sigma_{r+1}^P$.

**Proof.** Take a language in $\Sigma_i^P$. The membership characterization of the polynomial hierarchy says that a language belongs to $\mathsf{PH}$ exactly when it belongs to some existential level (`mem_PH_iff`). Choose the given index $i$ and its assumed membership in $\Sigma_i^P$ as the witness. This proves the inclusion.

**Key facts.** `Complexity.mem_PH_iff`.
