<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_split_of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time split recovery

**Claim.** Under the stated bounds on how the machine reaches its anchor state and performs each search round, some finite deterministic Turing machine computes the split-emitter function in time bounded by $B(n+1)^{r+2}$ for some natural number $B$.

**Proof.** First, a machine can compute the binary expansion of the input length in time linear in that length (`computesFunInTime_lengthBits`). The proof enlarges this bound to $(A+a)(|w|+1)^{r+1}$, where $a$ is the length-expansion machine's constant: the assumed start and round bounds are absorbed into this same polynomial bound. It then applies the loop-finding construction (`exists_loopFindTM`) with the current candidate string as the loop state, the one-round update as the step, and the specified acceptance test as the stopping condition. The invariant that the candidate has length at most $|w|+1$ holds initially and is preserved by each update (`e3_step_inv`). The given hypotheses ensure that the body reaches its anchor configuration within the required bound, and that each round either halts with the encoded split when the test accepts or returns to the anchor with the updated candidate. The loop construction therefore searches the successive candidates and returns the prescribed output. Its running time is bounded by the loop estimate `e3_loop_bound`; the proof uses this estimate to dominate the cost by a constant multiple of $(|w|+1)^{r+2}$. Finally, the loop's output agrees with the split-emitter function by `e3_loop_result`, yielding the claimed machine and constant $B$.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.exists_loopFindTM`, `Complexity.e3_step_inv`, `Complexity.e3_loop_bound`, `Complexity.e3_loop_result`.
