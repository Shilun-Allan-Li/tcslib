<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.mem_PH_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Hierarchy Characterization

**Claim.** A language belongs to the polynomial hierarchy if and only if it belongs to $\Sigma_i^P$ for some natural number $i$.

**Proof.** By definition, membership in $\mathsf{PH}$ gives an index $i$ for which the language lies in $\Sigma_{i+1}^P$, so it lies in some level of the hierarchy. Conversely, if the language lies in $\Sigma_i^P$, the level-inclusion theorem (`Complexity.SigmaP_subset_SigmaP_succ`) places it in $\Sigma_{i+1}^P$. Taking $i$ as the index in the union defining $\mathsf{PH}$ proves membership there.

**Key facts.** `Complexity.SigmaP_subset_SigmaP_succ`.
