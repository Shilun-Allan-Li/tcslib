<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordSkipTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Recording and Skip Run

**Claim.** After one more step than the length of the action encoding, the recording-and-skip machine preserves the initial input position, tape contents, output, and all work-tape head positions except that the table-tape head has advanced by the encoding length; its state is the successor phase marked done according to whether the action has a successor.

**Proof.** First split the action serialization into its fixed-width payload and its successor-state field. The serialization-reading lemma supplies the payload bits, their exact length, and the corresponding tape-cell assumptions for both portions (`Turing.StepBlock.actionBitsK_reads`). The fixed-width run result carries the machine through the payload and one dispatch step, placing it at the tag phase with the successor-state bits available (`Turing.StepBlock.recordSkipTM_fixed`). Split the remaining run using the iteration law for runs (`Turing.MultiTapeTM.runFrom_add`) and transfer it to the successor-field machine (`Turing.StepBlock.recordSkipTM_tail`). The successor-field run theorem consumes the state encoding and ends in the done state whose Boolean records whether the encoded state is present (`Turing.StepBlock.succFieldTM_run`). Combining the head movement from the fixed-width scan with the successor-field scan gives a total table-head advance equal to the full encoding length; the other heads do not move. The two stages preserve the input position, tape contents, and output, so the final configuration has exactly the asserted fields.

**Key facts.** `Turing.StepBlock.actionBitsK_reads`, `Turing.StepBlock.recordSkipTM_fixed`, `Turing.MultiTapeTM.runFrom_add`, `Turing.StepBlock.recordSkipTM_tail`, `Turing.StepBlock.succFieldTM_run`, `Turing.StepBlock.summary_ne_table`.
