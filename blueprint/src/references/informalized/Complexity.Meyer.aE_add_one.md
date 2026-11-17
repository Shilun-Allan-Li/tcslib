<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.aE_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Identity for Signed Encoding

**Claim.** For the signed integer encoding $a(e)$, adding one gives $|e|$ when $e<0$, and $|e|+1$ when $e\geq 0$.

**Proof.** Split according to whether $e$ is negative. If $e<0$, the encoding is the natural number represented by $-e-1$; adding one gives $-e$, which is the natural absolute value of $e$. If $e\geq0$, the encoding is $e$, so adding one gives $e+1=|e|+1$.
