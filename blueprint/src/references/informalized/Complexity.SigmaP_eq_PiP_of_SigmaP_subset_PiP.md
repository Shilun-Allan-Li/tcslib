<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.SigmaP_eq_PiP_of_SigmaP_subset_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Quantifier Classes

**Claim.** For every natural number $i$, if $\Sigma_i^P\subseteq\Pi_i^P$, then $\Sigma_i^P=\Pi_i^P$.

**Proof.** The assumed inclusion gives one direction. For the reverse, take $L\in\Pi_i^P$. The assumed inclusion gives $L\in\Sigma_i^P\subseteq\Pi_i^P$, so $L^c\in\Pi_i^P$. The complement characterization of $\Pi_i^P$ says precisely that $L^c\in\Pi_i^P$ is equivalent to $L\in\Sigma_i^P$ (`compl_mem_PiP_iff`). Thus every member of $\Pi_i^P$ is in $\Sigma_i^P$, and the two classes are equal.

**Key facts.** `Complexity.compl_mem_PiP_iff`.
