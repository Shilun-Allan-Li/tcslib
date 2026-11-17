<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.PiP_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Complement Alternation Classes

**Claim.** Whenever $i\le j$, every language in $\Pi_i^P$ also belongs to $\Pi_j^P$.

**Proof.** Take a language in $\Pi_i^P$. By definition, its complement belongs to $\Sigma_i^P$. Monotonicity of the existential alternation classes, applied to $i\le j$, places that complement in $\Sigma_j^P$. By the definition of $\Pi_j^P$, the original language therefore belongs to $\Pi_j^P$.

**Key facts.** `Complexity.SigmaP_mono`.
