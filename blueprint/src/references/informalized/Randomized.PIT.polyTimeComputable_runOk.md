<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_runOk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Run-Validity Test

**Claim.** The test that accepts exactly when the twice-projected component is nonempty and satisfies the stated termination condition is polynomial-time computable.

**Proof.** First, the nested projection $sW$ is polynomial-time computable. The nonemptiness test on its output is polynomial-time computable by composing $sW$ with the polynomial-time empty-string test (`polyTimeComputable_isNil`). The termination test on that same output is polynomial-time computable by composing $sW$ with the polynomial-time test `polyTimeComputable_isDone`. Negating the first Boolean test preserves polynomial-time computability (`polyTimeComputable_not`), and combining two such Boolean tests with conjunction preserves it (`polyTimeComputable_and`). Since `runOk` is exactly this conjunction, the result follows.

**Key facts.** `Complexity.polyTimeComputable_isNil`, `Randomized.PIT.polyTimeComputable_sW`, `Randomized.PIT.polyTimeComputable_isDone`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
