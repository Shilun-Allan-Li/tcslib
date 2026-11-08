<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_richWindow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constructing a Rich Window

**Claim.** Under the stated source-buffer, blank-tape, and separation hypotheses, the rich-window machine first reaches its final phase within the stated time bound. At that time it has written the centered word of $s$ zeros, one, and $s$ zeros on the destination tape, leaving all other configuration data unchanged; throughout the run its work-tape heads remain within the stated radius.

**Proof.** Set $w$ to the desired centered word, consisting of $s$ zeros, one, and $s$ zeros. First change the state label of the initial configuration to the copy machine’s sweep state. The copy-run theorem (`Turing.copyTM_run_ofCfg`) copies the buffered source word onto tape $\iota(0)$ and returns both heads to their starting positions. The hypotheses that the other embedded tapes are blank and that the chosen indices lie outside the embedding ensure that this copy does not interfere with the reserved tapes. The copied bank therefore has exactly the input format required by the cell-window construction.

Apply the cell-window run theorem (`Turing.rt_cellWindow_ready_run`) to this bank. It constructs the centered word on tape $\iota(1)$, reaches its exit state for the first time at the supplied bounded time, and controls all head positions. Regard the resulting tape segment as a buffer for $w$. The word-move theorem (`Turing.rt_moveWord_run`) transfers that segment from tape $\iota(1)$ to the destination tape and returns the relevant heads; the separation assumptions guarantee the source and destination are distinct. Finally, `Turing.clearTM_run_ofCfg` clears the temporary copy on tape $\iota(0)$ and returns that head. The buffer-mask identity (`Turing.rt_bufferMask`) justifies identifying the written finite segment with its buffered representation, including its boundary cells.

These three stages are joined in order by the seam-composition run theorem (`Turing.rt_copy_seam`). It preserves each stage’s first-exit property and combines their head-radius bounds. The copy, window, move, and clear stages have the respective time costs $2|ws|+2$, at most $18(s+|ws|)+32$, $4|w|+5$, and $2|ws|+2$. Since $|w|=2s+1$, their sum is at most $26(s+|ws|)+48$. At the final seam the temporary tape has been cleared and the destination contains precisely $w$ at its original head position; the unchanged components follow from the stage descriptions and the disjointness of the selected tapes. The combined radius estimate is the stated $2s+|ws|+3$.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.rt_bufferMask`, `Turing.rt_cellWindow_ready_run`, `Turing.rt_moveWord_run`, `Turing.clearTM_run_ofCfg`, `Turing.rt_copy_seam`.
