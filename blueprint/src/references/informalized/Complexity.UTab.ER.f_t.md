<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time register lookup

**Claim.** For any register state $e$, reading its time-budget coordinate returns the time budget stored in $e$.

**Proof.** The time-budget coordinate is $2$, and the register lookup function returns $e.t$ at that coordinate. Since $rT=2$, the lookup is exactly $e.t$.
