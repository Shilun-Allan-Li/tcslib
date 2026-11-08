<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_replay_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End of Replay Phase

**Claim.** After $|a|+1$ replay steps from the stated configuration, the extractor is in state $2$, at the same input position, with work head at $|a|$ and output $a$ if $first$ is true and empty otherwise.

**Proof.** Write $|a|+1$ as $|a|$ steps followed by one step. The replay-phase calculation ($\texttt{Turing.FinTM.f2_extract_replay}$) shows that the first $|a|$ steps leave the machine in replay state $1$, with work head at the end of $a$ and the required output. One additional step reads no tape symbol there, leaves the input position fixed, and changes the state to $2$ without modifying the tape or output. The one-step run equation ($\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}$) and the zero-move formula ($\texttt{Turing.moveInputPos_zero}$) give the stated configuration; the natural-position tape lookup is the list lookup formula ($\texttt{Turing.FinTM.bufferTape_nat}$).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_extract_replay`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
