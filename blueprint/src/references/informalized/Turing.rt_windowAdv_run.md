<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_windowAdv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Window Advancement

**Claim.** Given the stated buffered word on tape $0$, blank tape $2$, and the binary-value condition, the window-advancement machine first reaches its exit state within $12(s+|ws|)+20$ steps. Its heads stay within the stated radius, and its final configuration is the original configuration advanced by the centered word on tape $1$.

**Proof.** Set $\text{half}$ to the word of $s$ zeros. The repeat-machine theorem (`Turing.rt_repeat_run`) first writes this word on tape $1$, using tape $0$ as the source and tape $2$ as temporary storage. Its cost depends on the counter overhead; the bound `Turing.counterOverhead_le`, together with the hypothesis that the binary value of $ws$ is $s$, bounds that overhead. The run’s head-radius estimate is also inherited from the repeat-machine theorem.

Next, `Turing.rt_writeReleased_run` writes a single one on tape $1` and advances that tape’s head. The configuration now has the half-word followed by one. Apply the repeat-machine theorem again to write the second half-word of zeros. The head positions are tracked through the two advances, so this second pass appends the zeros after the one rather than overwriting the first half. The two stages and the intervening one-symbol write are joined using `Turing.rt_copy_seam`, which carries forward the first-exit and head-bound properties. The resulting tape word is precisely $s$ zeros, one, and $s$ zeros.

Finally, the identity `Turing.rt_advanceCfg_append` combines these successive tape advances into a single advancement by the centered word. The total duration is two repeat runs, the one-symbol write and its phase transitions; the counter-overhead bound gives at most $12(s+|ws|)+20$. The radius estimates for the repeated runs and intervening write yield $2s+|ws|+2$.

**Key facts.** `Turing.rt_repeat_run`, `Turing.counterOverhead_le`, `Turing.rt_writeReleased_run`, `Turing.rt_copy_seam`, `Turing.rt_advanceCfg_append`.
