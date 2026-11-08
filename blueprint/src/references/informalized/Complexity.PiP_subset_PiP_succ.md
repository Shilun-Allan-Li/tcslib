<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.PiP_subset_PiP_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consecutive Pi-Level Inclusion

**Claim.** For every $i\in\mathbb{N}$, every language in $\Pi_i^P$ belongs to $\Pi_{i+1}^P$.

**Proof.** Let $L\in\Pi_i^P$. The consecutive-level inclusion for the Sigma classes gives $\Sigma_i^P\subseteq\Sigma_{i+1}^P$ (\texttt{SigmaP\_subset\_SigmaP\_succ}). Applying this to the complement of $L$, which belongs to $\Sigma_i^P$ by the definition of $\Pi_i^P$, shows that the complement belongs to $\Sigma_{i+1}^P$. Hence $L\in\Pi_{i+1}^P$.

**Key facts.** `Complexity.SigmaP_subset_SigmaP_succ`.
