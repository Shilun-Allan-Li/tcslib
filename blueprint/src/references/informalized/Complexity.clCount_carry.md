<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_carry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Carry Phase of Increment

**Claim.** For every bit-list input $x$, valid input-head position $p$, bit lists $b$ and $s$, and prefix $u$, running the increment machine for one more than the carry count of $s$ steps from the stated carry configuration ends in rewind control, with the work head at $|u|+\operatorname{carry}(s)-1$, tape holding $u$ followed by the increment of $s$, and unchanged input head and empty output.

**Proof.** Induct on the suffix $s$, keeping the prefix arbitrary. For the empty suffix, one carry step takes the machine directly to rewind control and writes the incremented empty list; this is the base transition of the machine. For a nonempty suffix whose first bit is false, the carry count is zero, so the same one-step transition writes true at that position and enters rewind control, exactly producing the increment. If the first bit is true, the one-step transition writes false there, advances the work head by one, and remains in carry control. Apply the induction hypothesis to the remaining suffix with the enlarged prefix $u$ followed by false. Its carry count determines the remaining steps and its increment supplies the suffix after the newly written false. The iteration law for runs converts this first transition followed by the inductive run into the required total run; the resulting tape, head position, control state, input position, and output are the claimed ones.

**Key facts.** `Complexity.clCount_carry_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
