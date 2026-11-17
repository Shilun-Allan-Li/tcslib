<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.edge_E0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Endpoint Indicator

**Claim.** For every integer $e$, the conjunction that $e$ is nonnegative and its unsigned index is zero holds exactly when $e=0$.

**Proof.** Split into the cases $e<0$ and $e\ge 0$. If $e<0$, the sign bit is true, so its negation makes the conjunction false; also $e\ne0$, so the right-hand indicator is false. If $e\ge0$, the unsigned index is $e$ itself, and it is zero exactly when $e=0$. Thus both indicators agree in either case.
