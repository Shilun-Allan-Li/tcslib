<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.vx_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the First Bit String

**Claim.** For finite bit strings $x,U,t,a,j,p$, applying the total first projection twice to $\langle\langle x,U\rangle,\langle\langle t,a\rangle,\langle j,p\rangle\rangle$ gives $x$.

**Proof.** The first projection of the outer encoded pair recovers $\langle x,U\rangle$. Applying the first projection to this pair then recovers $x$. Both parses succeed because each pair encoding has a separator following the doubled bits of its first component.
