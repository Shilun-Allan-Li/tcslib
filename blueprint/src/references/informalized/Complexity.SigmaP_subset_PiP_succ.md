<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_subset_PiP_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Level in the Next Universal Level

**Claim.** For every natural number $i$, every language in $\Sigma_i^P$ belongs to $\Pi_{i+1}^P$.

**Proof.** Let $L\in\Sigma_i^P$. The complement characterization of the universal class gives $L^c\in\Pi_i^P$ (`compl_mem_PiP_iff`). The inclusion of the universal level in the next existential level then yields $L^c\in\Sigma_{i+1}^P$ (`PiP_subset_SigmaP_succ`). By definition, this means $L\in\Pi_{i+1}^P$.

**Key facts.** `Complexity.compl_mem_PiP_iff`, `Complexity.PiP_subset_SigmaP_succ`.
