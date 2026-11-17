<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Window-Loop Round

**Claim.** Under the test-run and step-run hypotheses, one loop round has the stated positive bounded duration, avoids stop states before its endpoint, stays within the stated head-position bound, and ends in the halted stop state, the updated anchor configuration, or the left-exit stop state according to the cases in the claim.

**Proof.** Write $L$ for the joined-field length of the record and let $B$ be the assertion that every work-head position stays within $(C_t+C_s+3)(\operatorname{recordLength}(k,|x|,s)+1)$ of its initial position. The initial configuration satisfies $B$. First, the anchor phase takes one stationary dispatch step into the test phase; applying the phase-segment result gives a segment of length one, preserves $B$, and introduces no stop state.

From the anchor configuration, run the test machine for the supplied duration. The selected-tape embedding identifies its run with the test row of the hosted machine (by \texttt{Turing.embedEmitCfg\_select} and \texttt{Turing.embedEmitTM\_runFrom}); the embedding facts \texttt{Turing.embedEmitCfg\_eq}, \texttt{Turing.embedEmitCfg\_selected\_pos}, and \texttt{Turing.embedEmitCfg\_unselected} identify its endpoint and show that the other tapes and heads are unchanged. The length identity \texttt{Turing.joinFields\_cfgRecord\_length} converts $L$ to the stated record-length bound. The test avoids both transition states before its endpoint, so the phase-segment result applies: if $c$ is halted, the test transitions to the halted stop state. Otherwise it transitions to the step phase. In either case, the head bound follows from the test's displacement bound and the chosen larger radius.

In the nonhalted case, apply the same reasoning to the supplied step-machine run. Its guard excludes the two step transition states before the endpoint, so the phase-segment result follows the step row throughout that run. If $M(c)$ is within the window, the endpoint has state $s_y$ and its record tape agrees cell by cell with the patch of the updated record; the other tapes are unchanged. The final phase transition returns to the anchor phase. If $M(c)$ lies outside the window, the endpoint has state $s_n$, and the phase transition instead enters the left-exit stop state. The step displacement bound again implies $B$ throughout.

Concatenate the dispatch, test, and (when needed) step segments using segment concatenation (\texttt{Turing.Segment.trans}). The respective run-length bounds, together with the record-length identity, give the claimed upper bound; the dispatch step ensures the total length is positive. The test and step guards, and the phase-segment result, ensure that no stop state occurs strictly before the endpoint. The bound $B$ holds across the concatenated segments, giving the claimed full-round head-position bound.

**Key facts.** `Turing.embedEmitCfg_select`, `Turing.embedEmitTM_runFrom`, `Turing.embedEmitCfg_eq`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitCfg_unselected`, `Turing.joinFields_cfgRecord_length`, `Turing.wl_phase_segment`, `Turing.Segment.trans`.
