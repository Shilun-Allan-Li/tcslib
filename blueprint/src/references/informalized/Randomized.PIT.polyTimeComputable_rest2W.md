<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_rest2W -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Second Rest Transformation

**Claim.** Applying the unary rest transducer twice to the suffix obtained by deleting the first four bits is polynomial-time computable.

**Proof.** The second rest transformation first applies the middle-word function, which deletes the first four bits and performs one unary rest transduction, and then applies the unary rest transducer once more. The middle-word function is polynomial-time computable (`Randomized.PIT.polyTimeComputable_midW`), as is the unary rest transducer (`Complexity.BinArith.polyTimeComputable_uRest`). Closure under composition (`Complexity.PolyTimeComputable.comp`) gives polynomial-time computability of their composite.

**Key facts.** `Randomized.PIT.polyTimeComputable_midW`, `Complexity.BinArith.polyTimeComputable_uRest`, `Complexity.PolyTimeComputable.comp`.
