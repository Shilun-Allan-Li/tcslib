<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.reg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Register Bound

**Claim.** If each of the fifteen entries of a register record is at most $B$, then every coordinate of the configuration built from its register vector is at most $B$, regardless of the optional label and result.

**Proof.** The record bound supplies one inequality for each of its fifteen fields. The register vector lists those fields in order, so for any coordinate among $0$ through $14$, its value is the corresponding field and is at most $B$. The optional label and result do not affect the register vector, which is the only part used by the coordinate bound.
