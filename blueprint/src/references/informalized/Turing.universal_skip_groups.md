<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_skip_groups -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping Consecutive Record Groups

**Claim.** After skipping the serialized records of all groups, the interpreter reaches the state-rewind phase remembering the record index, with the table cursor past the group bits and the state tape and cursor advanced by the number of groups.

**Proof.** Induct on the list of groups. With no groups, the group-phase transition detects the end of the state window and enters the state-rewind phase in one step. The empty-window fact identifies the resulting tape with the required zero-remaining window (`Turing.universalStateWindow_end`). For a nonempty list, the first group has nine actions. The interpreter reads the unary marker for that group, erases that marker, and enters fixed-field skipping; the window read and erase identities (`Turing.universalStateWindow_read`, `Turing.universalStateWindow_erase`) give the updated state tape. The single-group record-skipping result then advances over the first group's serialized bits. Apply the induction hypothesis to the remaining groups, taking the table prefix and consumed-cell count to include this first group. The run-addition law composes these stages, while the one-step run identities and the interpreter step rule justify the transitions and their configuration updates (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`, `Turing.universalStateWindow_end`, `Turing.universalStateWindow_read`, `Turing.universal_skip_records`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.universalStateWindow_erase`.
