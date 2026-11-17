<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTrajectory_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time production of native trajectories

**Claim.** If the input transformation $y$ and the unary length function $T$ are polynomial-time computable, then the serialized trajectory of $M$ on $y(x)$ through time $T(x)$, inclusive, is polynomial-time computable.

**Proof.** First, the record-word construction is polynomial-time computable from the hypotheses on $y$ and the unary encoding of $T$ (`Complexity.clRecordWords_native`). The record-output machine then converts those record words to the desired serialized trajectory in time bounded by a fixed quadratic polynomial in the record-word input length (`Complexity.clRecordOutput_quadratic`). The polynomial-time composition principle (`Complexity.clNative_image`) combines these computations. Its required time bound is exactly the one supplied by the record-output estimate, so the trajectory function is polynomial-time computable.

**Key facts.** `Complexity.clRecordWords_native`, `Complexity.clNative_image`, `Complexity.clRecordOutput_quadratic`.
