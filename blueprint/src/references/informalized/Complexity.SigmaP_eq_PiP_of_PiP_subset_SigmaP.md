<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.SigmaP_eq_PiP_of_PiP_subset_SigmaP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of adjacent quantifier classes

**Claim.** For every natural number $i$, if $\Pi_i^P\subseteq\Sigma_i^P$, then $\Sigma_i^P=\Pi_i^P$.

**Proof.** The assumed inclusion gives $\Pi_i^P\subseteq\Sigma_i^P$. For the reverse inclusion, take $L\in\Sigma_i^P$. The complement characterization says exactly that $L^c\in\Pi_i^P$ (Complexity.compl_mem_PiP_iff). By the assumed inclusion, $L^c\in\Sigma_i^P$, which by the definition of $\Pi_i^P$ means $L\in\Pi_i^P$. Thus both inclusions hold.

**Key facts.** `Complexity.compl_mem_PiP_iff`.
