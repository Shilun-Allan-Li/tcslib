<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.coNP_subset_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP at Every Positive Universal Level

**Claim.** For every natural number $i\ge 1$, every language in coNP belongs to $\Pi_i^{\mathrm P}$.

**Proof.** The identity $\Pi_1^{\mathrm P}=\mathrm{coNP}$ identifies the given language as an element of the first universal level. Since $1\le i$, monotonicity of the universal hierarchy places every language at level $1$ in level $i$.

**Key facts.** `Complexity.PiP_one`, `Complexity.PiP_mono`.
