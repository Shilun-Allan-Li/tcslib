<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_midW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Middle Word

**Claim.** Deleting the first four bits of a Boolean word and applying the specified unary rest transducer is polynomial-time computable.

**Proof.** The transformation is the composition of two polynomial-time functions: first delete the initial four bits, then apply the unary rest transducer. The first operation is polynomial-time computable (`Randomized.PIT.polyTimeComputable_bodyW`), and the second is polynomial-time computable (`Complexity.BinArith.polyTimeComputable_uRest`). Closure under composition (`Complexity.PolyTimeComputable.comp`) therefore gives polynomial-time computability of the resulting function.

**Key facts.** `Randomized.PIT.polyTimeComputable_bodyW`, `Complexity.BinArith.polyTimeComputable_uRest`, `Complexity.PolyTimeComputable.comp`.
