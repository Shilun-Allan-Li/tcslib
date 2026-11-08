<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_runWith_handoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Handoff to the verifier phase

**Claim.** After the prescribed choice word is processed, the guess-and-run machine is in the run phase at the configuration obtained from $c_P$ by replacing the indicated block on tape $j$ with the next $m$ bits of $w$.

**Proof.** Split $w$ into five consecutive segments, each consisting of a prefix, one distinguished bit, and a remainder, at the successive lengths $T_P$, $m+1$, $1$, and $m+3$. The total length hypothesis forces the final remainder to be empty. The first segment has length $T_P$, and the next segment's prefix supplies exactly the $m$ bits used in the replacement; consequently $(w.drop (T_P+1)).take m$ is that prefix truncated to length $m$.

First, the setup phase simulates $P$ for $T_P$ steps. Since $c_P$ is in state $p_{\mathrm{exit}}$, the next input bit dispatches the machine into the writer phase. The first-visit hypothesis ensures there was no earlier dispatch, so this simulation uses precisely the initial segment of length $T_P$.

The writer consumes the next $m+1$ bits. The first $m$ are written consecutively on tape $j$, and the blank at the next cell makes the bounded writer stop; its final head position is one cell beyond that blank. This is the block-writing behavior of `ndWriterTM_run_block`. The skip phase then moves one cell right, crossing the blank after the guessed block, and dispatches into the rewind phase. The assumed blank at the original cell immediately left of the head ensures the skip phase encounters the required blank at its endpoint.

The rewind phase moves left across the guessed block until it reaches the blank immediately before its start, then moves right once to the block's start and dispatches into the run phase. The tape comparison uses the buffer's value at negative one (`bufferTape_left`) and its values at natural indices (`bufferTape_nat`); together with the endpoint and blank hypotheses, these show the rewind leaves the intended word on tape $j$ and restores its head to the original position. Other tapes, head positions, input position, and output are unchanged throughout these auxiliary phases.

The phase-host transition theorem `phaseHostND_run` justifies each phase's simulation and its single dispatch step; the deterministic-to-choice-input correspondence `MultiTapeTM.toNDTM_runWith` identifies the setup, skip, and rewind runs with their deterministic runs. Concatenating the four segments and their dispatch bits therefore yields the asserted configuration in the run phase at $q_{\mathrm{entry}}$. The final configuration comparison is componentwise: its tape contents agree with the block-replacement construction, and its head positions return to those of $c_P$.

**Key facts.** `Turing.guessRun_split`, `Turing.MultiTapeTM.toNDTM_runWith`, `Turing.NDTM.phaseHostND_run`, `Turing.ndWriterTM_run_block`, `Turing.skipTM_run_ofCfg`, `Turing.skipBackTM_run_ofCfg`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.NDTM.runWith_append`, `Turing.guessRun_mapState_mapState`.
