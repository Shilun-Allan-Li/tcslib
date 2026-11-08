<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.compl_mem_SigmaP_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Characterization of Existential Levels

**Claim.** For every $i\ge 0$ and binary language $L$, $L^c\in\Sigma_i^P$ if and only if $L\in\Pi_i^P$.

**Proof.** By definition, $L\in\Pi_i^P$ means precisely that $L^c\in\Sigma_i^P$. The two sides are the same membership condition, so the equivalence holds directly.
