<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.gu_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested witness projection

**Claim.** For bit strings $x,U,t,u,j,p$, applying the total first projection twice to the second component of the outer encoding returns $u$.

**Proof.** The projection $\mathrm{gu}$ first takes the second component of the outer encoding, then takes the first component twice. Decoding the outer pair reaches $\langle\langle u,j\rangle,p\rangle$; the first projection reaches $\langle u,j\rangle$, and the next first projection returns $u$.
