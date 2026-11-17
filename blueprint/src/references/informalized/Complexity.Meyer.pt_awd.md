<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_awd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of the AW Operations

**Claim.** For every operation $A$ in the six specified cases, the function $\mathrm{awd}(C_w,c_w,A)$ is polynomial-time computable.

**Proof.** Proceed by cases on the operation. Copying the second decoded component is polynomial-time computable by the result for $va$ (`pt_va`). Incrementing that component is the composition of $va$ with fixed-width increment, with overflow replaced by the empty word; composition preserves polynomial-time computability (`PolyTimeComputable.comp`), and the increment operation is polynomial-time computable (`pt_inc`). Producing the all-zero word of the specified length is the constant-symbol replication operation (`pt_rep` with false); incrementing this word is again its composition with fixed-width increment, so `pt_inc` and `PolyTimeComputable.comp` apply. For the final two cases, producing the length encoding followed by zeros is polynomial-time computable by `pt_bjw`; incrementing it follows by composing with `pt_inc`, again using closure under composition.

**Key facts.** `Complexity.Meyer.pt_va`, `Complexity.Meyer.pt_inc`, `Complexity.PolyTimeComputable.comp`, `Complexity.Meyer.pt_rep`, `Complexity.Meyer.pt_bjw`.
