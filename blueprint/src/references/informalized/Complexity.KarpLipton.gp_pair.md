<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.gp_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested payload projection

**Claim.** For bit strings $x,U,t,u,j,p$, applying the total second projection twice to the nested pair encoding returns $p$.

**Proof.** The projection $\mathrm{gp}$ takes the second component twice. The decoder recovers the two original components of each encoded pair, so the first projection reaches the inner pair $(\langle u,j\rangle,p)$ and the second extracts $p$.
