<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a counter row

**Claim.** Starting from a source configuration and tag, the recorder copies the binary representations of all counter values into the record in field order, reaching clock-test control in at most $F(3W+4)+1$ steps while preserving the source configuration, tag, clock budget, and logical time.

**Proof.** Apply the first-row traversal result (`clRow_first`) to the $F$ counter fields and their binary representations. The positivity condition needed there holds because $F=2(1+M.k)>0$. This gives a run of at most $F(3W+4)$ steps that traverses the fields, appends their self-delimiting encodings in order, and ends at the final row-copy control. The embedding of the row-copy machine into the recorder is handled by `clPlaced_run`: its guard is that the row machine has not yet reached its final control at any earlier time, exactly the nonarrival property supplied by `clRow_first`. The frame identity `clRec_row_frame` identifies the embedded initial row configuration with the recorder’s configuration, while the inactive-row and frame identities (`clRec_row_inactive` and `clRec_row_frame`) align the terminal embedded configuration with the recorder’s row-complete configuration. One additional recorder transition leaves row-copy control for clock-test control, preserving the copied record and all source data. Thus the total is at most $F(3W+4)+1$.

**Key facts.** `Complexity.clRow_first`, `Complexity.clPlaced_run`, `Complexity.clRec_row_frame`, `Complexity.clRec_row_inactive`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
