<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.edge_E1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Endpoint Indicator

**Claim.** For every integer $e$, the conjunction that $e$ is negative and its unsigned index is zero holds exactly when $e+1=0$.

**Proof.** Split into the cases $e<0$ and $e\ge0$. When $e\ge0$, the sign bit is false, so the conjunction is false; also $e+1>0$, so the right-hand indicator is false. When $e<0$, the unsigned index is $-e-1$, a natural number. It is zero exactly when $-e-1=0$, equivalently $e+1=0$. Hence the indicators agree in both cases.
