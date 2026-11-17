<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.gj_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested index projection

**Claim.** For bit strings $x,U,t,u,j,p$, decoding the nested pair encoding by the prescribed projections extracts $j$.

**Proof.** By definition, $\mathrm{gj}$ takes the second component of the outer pair, then the first component of that result, and finally its second component. The pairing decoder reverses the encoding: it recovers the two original strings from each pair. Applying these three projections to the given nested encoding therefore successively reaches the pair containing $(u,j)$ and then extracts $j$.
