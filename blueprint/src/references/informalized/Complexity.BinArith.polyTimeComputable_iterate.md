<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.polyTimeComputable_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bounded Iteration

**Claim.** Under the stated polynomial bound on all intermediate word lengths, the result of applying $g$ the specified number of times to $u(z)$ is polynomial-time computable.

**Proof.** For each input $z$, initialize the block loop with a nonempty counter marker, a unary counter of length $a(|z|+1)^k$, and the payload $u(z)$. This initialization is polynomial-time computable by the unary-word construction and pair-encoding closure (`polyTimeComputable_polyUnary`, `PolyTimeComputable.pairEncode`), and the countdown initialization theorem supplies the complete encoded start state (`BlockLoop.polyTimeComputable_countdownInit`). Each guarded round implements one application of $g$ while maintaining the counter and payload; the guarded-step and emission constructions are polynomial-time computable (`polyTimeComputable_guardLoop`, `BlockLoop.polyTimeComputable_emit`). The uniform length hypothesis ensures the iterates remain within a polynomial size bound, which is the hypothesis needed by the bounded-loop theorem (`BlockLoop.polyTimeComputable_of_loop`). To identify the loop’s output, use the block-loop output identity (`BlockLoop.loop_output`): after the prescribed number of rounds, the counter is exhausted and the payload is $g^{[a(|z|+1)^k]}(u(z))$. The intermediate-length estimate is exactly the assumed bound, applied to each iteration index. Therefore the loop output is the desired function, and the bounded-loop theorem gives its polynomial-time computability.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BlockLoop.polyTimeComputable_countdownInit`, `Complexity.BinArith.polyTimeComputable_guardLoop`, `Complexity.BlockLoop.polyTimeComputable_emit`, `Complexity.BinArith.length_iterate_guardLoop_le`, `Complexity.BlockLoop.loop_output`, `Complexity.BlockLoop.polyTimeComputable_of_loop`.
