<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Existential Hierarchy

**Claim.** Whenever $i\le j$, every language in $\Sigma_i^P$ belongs to $\Sigma_j^P$.

**Proof.** Induct on the inequality $i\le j$. If $i=j$, the inclusion is the identity. In the successor step, the induction hypothesis gives $\Sigma_i^P\subseteq\Sigma_j^P$ for the preceding pair, and the successive-level inclusion gives $\Sigma_j^P\subseteq\Sigma_{j+1}^P$ (`SigmaP_subset_SigmaP_succ`). Composing these inclusions proves the result.

**Key facts.** `Complexity.SigmaP_subset_SigmaP_succ`.
