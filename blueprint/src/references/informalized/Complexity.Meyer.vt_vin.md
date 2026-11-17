<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.vt_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the Time String

**Claim.** For arbitrary bit strings $x,U,t,a,j,p$, applying the total second projection and then the total first projection twice to $\langle\langle x,U\rangle,\langle\langle t,a\rangle,\langle j,p\rangle\rangle$ recovers $t$.

**Proof.** The outer pair's second projection gives $\langle\langle t,a\rangle,\langle j,p\rangle\rangle$. Taking its first projection gives $\langle t,a\rangle$, and taking the first projection once more yields $t$. The encodings parse successfully at each stage, so the total projections return the specified components.
