<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_exists_boundFieldTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded field-writing machine

**Claim.** There is a finite-state machine that, from the prescribed entry configuration, writes the binary expansion of $|x|+1$ on a spare destination tape within linear time, avoids its exit state until completion, and obeys the stated head-radius bound.

**Proof.** Begin with the clean digit-bound machine supplied by `rt_exists_cleanDigitBoundTM`. Its computation, run on the embedded machine and the given configuration after renaming the entry state, writes the binary expansion of $|x|+1$ on the first embedded tape, reaches its exit state for the first time within $C(|x|+1)$ steps, and has head displacement bounded by $C((|x|+1).bits.length+1)$. The final construction first embeds this machine on the chosen tapes and then composes it with a word-moving machine, using `rt_copy_seam` to join the two runs. The word-moving machine transfers the written binary word from tape $\iota(0)$ to the spare tape $dst$; its run theorem (`rt_moveWord_run`) gives completion in $4w.length+5$ steps, avoids its exit state earlier, and bounds its head movement by $w.length+4$, where $w$ is the binary word. The source tape’s contents give the required buffer hypothesis for this transfer. The two head-radius estimates are both bounded by the larger radius $B=(C+10)((|x|+1).bits.length+1)$, and the word length is at most $|x|+1$. The seam result therefore gives the total run, first-exit property, and radius bound. Its endpoint description says the destination contains the word while the source’s copied interval is cleared; because the embedded computation’s source tape began blank and the destination was outside the embedding, the final buffer-mask identity (`rt_bufferMask`) simplifies the combined tape update to exactly the requested destination contents, leaving every other tape cell unchanged. The added transfer time is absorbed by the constant $C+10$ in the linear time bound.

**Key facts.** `Turing.rt_exists_cleanDigitBoundTM`, `Turing.rt_moveWord_run`, `Turing.rt_copy_seam`, `Turing.rt_bufferMask`.
