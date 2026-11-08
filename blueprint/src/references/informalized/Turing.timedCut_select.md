<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_select -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selecting a Transition Record

**Claim.** Under the stated group lengths and table decomposition, the interpreter reaches the action-reading phase at the beginning of the selected record, with its action register cleared and its state tape reset to unary zero, after the specified number of steps.

**Proof.** Write $P_G$ for the serialization of all group records and $P_B$ for the serialization of the records before the selected one. First apply the group-skipping result (`timedCut_skip_groups`): the interpreter passes over all groups, reaches the state-rewind phase, and its state tape has no remaining unary symbols. The empty-window and zero-window identities (`universalStateWindow_empty`, `universalStateWindow_zero`) identify this tape with the unary-zero state tape. Next, the state-rewind result (`timedCut_state_rewind`) scans back to cursor 1 and chooses the continuation determined by the selected index. If the index is zero, there are no preceding records, so this continuation is already action-reading at the start of the selected record. Otherwise, the preceding-record skipping result (`timedCut_skip_records`) passes over exactly those records and reaches the same action-reading phase at cursor $|L|+|P_G|+|P_B|$. Finally, decompose the total duration into the group-scan, rewind, and preceding-record segments. Run composition (`Turing.MultiTapeTM.runFrom_add`) combines the segments; the displayed duration is their sum.

**Key facts.** `Turing.timedCut_skip_groups`, `Turing.universalStateWindow_empty`, `Turing.universalStateWindow_zero`, `Turing.timedCut_state_rewind`, `Turing.timedCut_skip_records`, `Turing.MultiTapeTM.runFrom_add`.
