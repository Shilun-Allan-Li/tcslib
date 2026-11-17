<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.gx_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested input projection

**Claim.** For bit strings $x,U,t,u,j,p$, applying the total first projection twice to $\langle\langle x,U\rangle,t\rangle$ returns $x$.

**Proof.** The projection $\mathrm{gx}$ takes the first component twice. The decoder recovers the original components of each encoded pair, so the first projection returns $\langle x,U\rangle$ and the second returns $x$.
