<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.polyTimeComputable_shiftRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Shift Run

**Claim.** The shift-run function, which initializes a configuration from the total projections of an input, iterates the shift step for the input length plus one iterations, and returns the nested total second projection, is polynomial-time computable.

**Proof.** The initial configuration, formed by pair-encoding the total first projection with an encoding of the total second projection and the empty word, is polynomial-time computable by projection, constant-output, and pair-encoding closure. To apply the polynomial-time iteration result, bound the length of every intermediate iterate. After $i$ steps, the shift-step length estimate supplies a representation with output and word lengths whose sum is at most the initial word length plus $i$ times a linear expression in the initial context length. The total projections have length at most the original input length, and $i$ is at most that length plus one. Thus the intermediate configuration length is bounded by a quadratic polynomial in the input length; the proof uses the elementary inequality $m+1\leq(m+1)^2$ to put the estimate in the required form. Polynomial-time iteration now applies to the shift step for the specified input-length-plus-one number of iterations. Composing with the final nested second projection yields the claimed shift run.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.PIT.polyTimeComputable_shStep`, `Randomized.PIT.iterate_shStep_le`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.PolyTimeComputable.comp`.
