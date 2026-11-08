<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time block output

**Claim.** The output function that returns the empty string when the first projection is empty, returns $\mathrm{out}(s)$ when the first projection is nonempty and the first projection of the second projection is empty, and otherwise returns the empty string is polynomial-time computable.

**Proof.** The empty-string function is polynomial-time computable (`polyTimeComputable_const`). The first-projection empty test is polynomial-time computable (`polyTimeComputable_headNil`), and the nested empty test is polynomial-time computable (`polyTimeComputable_countdownNil`). Use the nested test to choose between $\mathrm{out}$ and the empty string; this conditional is polynomial-time computable by closure under conditionals (`polyTimeComputable_ite`). Then use the first-projection test to choose between that result and the empty string, applying the same closure once more. This is exactly the specified output function.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.BlockLoop.polyTimeComputable_headNil`, `Complexity.BlockLoop.polyTimeComputable_countdownNil`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_ite`.
