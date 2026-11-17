<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordTM_execute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Recorded Action

**Claim.** After $4k+5$ steps, the record machine's configuration is the result of applying the payload action—formed from the original action with halting successor state and the current summary symbol—to the configuration storing the full record and with the record-tape head advanced by $4k+4$.

**Proof.** Write the run of length $4k+5$ as the step following the first $4k+4$ steps. The partial-reading lemma says that this intermediate configuration stores all record bits and has its record head advanced by $4k+4$ (\texttt{recordTM\_read}). Its summary-tape symbol is still the original one because the summary tape is distinct from the record tape (\texttt{summary\_ne\_table}). At this point the machine applies its payload transition. The prefix encoding hypothesis guarantees that decoding the stored bits gives the original input movement, work-tape actions, and output, with the successor state replaced by halting (\texttt{payload\_correct}). Thus this final transition is exactly the stated payload action applied to the fully read configuration; the run-length decomposition is \texttt{runFrom\_succ\_eq\_step'}.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.StepBlock.recordTM_read`, `Turing.StepBlock.summary_ne_table`, `Turing.StepBlock.payload_correct`.
