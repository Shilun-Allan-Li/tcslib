<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.NP_subset_SigmaP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Lies in Every Positive Existential Level

**Claim.** For every natural number $i$ with $1\le i$, every language in $\mathrm{NP}$ belongs to $\Sigma_i^P$; hence $\mathrm{NP}\subseteq\Sigma_i^P$.

**Proof.** The equality $\Sigma_1^P=\mathrm{NP}$ (`SigmaP_one`) identifies $\mathrm{NP}$ with the first existential level. Since $1\le i$, monotonicity of the existential hierarchy (`SigmaP_mono`) gives $\Sigma_1^P\subseteq\Sigma_i^P$. Combining these yields the claimed inclusion.

**Key facts.** `Complexity.SigmaP_one`, `Complexity.SigmaP_mono`.
