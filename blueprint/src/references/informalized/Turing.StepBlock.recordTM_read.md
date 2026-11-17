<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordTM_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Partial Record

**Claim.** After $r\le4k+4$ steps, the record machine's configuration is exactly the one storing position $r$, the read prefix of the record with false entries thereafter, and a record-tape head advanced by $r$.

**Proof.** Proceed by induction on $r$. At zero steps the configuration is unchanged, and the claimed stored position, blank record, and head location agree with the initial state. For the successor step, assume the description at time $r$ and use $r<4k+4$. The record-tape head therefore reads the next cell, whose symbol is the $(r+1)$st record bit by hypothesis. The machine moves that head one position forward and updates the stored record by placing this bit at position $r$; the resulting function has the record bits precisely before position $r+1$ and false entries thereafter. All other tapes, the input position, and the output remain unchanged. The run at time $r+1$ is one machine step after time $r$ (\texttt{runFrom\_succ\_eq\_step'}), and the transition has exactly this tape-action effect (\texttt{step\_of\_tapeAction\_move}).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.step_of_tapeAction_move`.
