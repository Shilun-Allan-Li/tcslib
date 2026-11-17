<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordTM_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head-Movement Bounds During Recording

**Claim.** During the record machine's first $4k+5$ steps, all stated head-displacement bounds hold, and the record-tape head advances by $\min(u,4k+4)$ while the summary-tape head stays fixed.

**Proof.** Fix a time $u\le 4k+5$ and split into the final time and the earlier times. At $u=4k+5$, the execution lemma identifies the run with the payload action applied to the fully read record configuration (\texttt{recordTM\_execute}). The payload leaves the first $k$ tape heads unchanged except for their prescribed action displacements, moves the input head according to the action, and leaves the summary head fixed. The first $k$ tapes are distinct from the record tape (\texttt{mirror\_ne\_table}); for their displacement bound, applying any action moves a work-tape head by at most one (\texttt{workTapePos\_apply\_le}). The two auxiliary heads satisfy the claimed bounds by their explicit payload movements, and the input displacement is at most one. For $u<4k+5$, we have $u\le4k+4$, so the partial-reading lemma identifies the configuration with the record after exactly $u$ cells have been read (\texttt{recordTM\_read}). The record head has advanced by $u=\min(u,4k+4)$; all other heads remain fixed, giving the required bounds and equalities. The summary and record tapes are distinct (\texttt{summary\_ne\_table}).

**Key facts.** `Turing.StepBlock.recordTM_execute`, `Turing.StepBlock.mirror_ne_table`, `Turing.workTapePos_apply_le`, `Turing.StepBlock.recordTM_read`, `Turing.StepBlock.summary_ne_table`.
