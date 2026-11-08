<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_countdown -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial time for countdown output

**Claim.** Under the given polynomial-time hypotheses, length-growth condition, and output identity, the function $f$ is polynomial-time computable.

**Proof.** The proof reduces the claim to the general polynomial-time theorem for a bounded loop. First, the two assumed polynomial-time maps for the parsed head and next state make the block-loop step polynomial-time computable (`polyTimeComputable_step`); the output operation is polynomial-time computable as well (`polyTimeComputable_emit`). The initialization function is polynomial-time computable because it combines the constant string $h_0$, the unary countdown of length $a'(|x(z)|+1)^{k'}$, and $r(z)$ (`polyTimeComputable_countdownInit`). Next, the stated live-state length bound yields a one-step bound on the step's weighted length, where the weight includes the parsed countdown length (`length_step_le`). Iterating this estimate gives a linear bound in the initial state length for every iterate (`length_iterate_le_of_slack`), with slack parameter $c+2$; its required numerical inequalities hold because $c$ is a natural number. Finally, the assumed identity says that the loop's concatenated outputs are exactly $f(z)$ for every input. These ingredients meet the hypotheses of the general bounded-loop closure theorem, which concludes that $f$ is polynomial-time computable (`polyTimeComputable_of_loop`).

**Key facts.** `Complexity.BlockLoop.polyTimeComputable_step`, `Complexity.BlockLoop.polyTimeComputable_emit`, `Complexity.BlockLoop.polyTimeComputable_countdownInit`, `Complexity.BlockLoop.length_step_le`, `Complexity.BlockLoop.length_iterate_le_of_slack`, `Complexity.BlockLoop.polyTimeComputable_of_loop`.
