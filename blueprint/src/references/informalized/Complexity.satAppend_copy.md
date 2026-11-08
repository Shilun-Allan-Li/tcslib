<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satAppend_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending the Remaining Suffix

**Claim.** If $x=pr$, then starting in the copy state with the work tape holding $wp$ and its head at the end of that word, the appender reads and copies the remaining suffix $r$. After $|r|+1$ steps it is in the copy state with the work tape holding $wx$ and its head one position before the end.

**Proof.** Induct on the suffix $r$. If it is empty, the equality $x=p$ identifies the input with the already copied prefix. The input head is at the clamped position for the end of the input, so it reads a blank. The copy-state transition leaves the tape unchanged, moves the work head one position left, and changes to the copy state as required; the run-length facts identify this single step with the stated run. For $r=b::r'$, the head is at the position for the end of $p$, where the input symbol is $b$ (`satStreamPos_read`). The copy transition writes $b$ in the next work-tape cell, advances the input and work heads, and remains in the copy state. The tape update is exactly the extension from $wp$ to $wpb$ (`bufferTape_append`), and the input-head advance gives the position for the end of $pb$ (`satStreamPos_succ`). The run decomposition into one step followed by the remaining run (`runFrom_succ_eq_step`) reduces the claim to the induction hypothesis with prefix $pb$ and suffix $r'$. The zero-step run identity and the fact that a zero input-head move leaves its position fixed (`runFrom_zero`, `moveInputPos_zero`) account for the base-case configuration details.

**Key facts.** `Complexity.satStreamPos_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.satStreamPos_succ`, `Turing.FinTM.bufferTape_append`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
