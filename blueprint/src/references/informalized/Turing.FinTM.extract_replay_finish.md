<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_replay_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End of Buffer Replay

**Claim.** After exactly $|a|+1$ steps from replay state with buffer $a$, work head at zero, and empty output, the extractor is in suffix-scanning state with work head at $|a|$ and output $a$ if the first flag is true, and empty otherwise.

**Proof.** Apply the replay invariant at time $|a|$: the machine is still in replay state, its work head is at $|a|$, and its output is the prefix of $a$ of length $|a|$ when the first flag is true, and empty otherwise. Since that prefix is all of $a$, the work head reads no symbol. The replay-state transition on an empty work cell changes to suffix-scanning state, leaves the input head and work tape unchanged, and emits nothing. Thus the output remains as claimed and the work head remains at $|a|$. The one-step run equation (Lean name `runFrom_succ_eq_step'`) identifies this transition with the requested run of length $|a|+1$. The zero-movement input-head fact (`moveInputPos_zero`) and the natural-position buffer reading rule (`bufferTape_nat`) justify the configuration coordinates.

**Key facts.** `Turing.FinTM.extract_replay`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
