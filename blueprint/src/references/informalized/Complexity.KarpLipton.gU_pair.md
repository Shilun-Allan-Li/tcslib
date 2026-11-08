<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.gU_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the inner pair's second component

**Claim.** For any bit strings $x,U,t$, applying $g_U$ to the nested pair encoding $\langle\langle x,U\rangle,t\rangle$ returns $U$.

**Proof.** The outer pair decoder recovers $\langle x,U\rangle$ as its first component. Applying the first-component decoder again recovers $x$ as the inner first component, and the second-component decoder recovers $U$. Since the pair encoding is decoded exactly into its original components, the outer second component $t$ does not affect this result.
