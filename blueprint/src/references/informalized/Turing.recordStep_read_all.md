<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_read_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Configuration Record

**Claim.** From a complete record of a configuration and tag, the record machine reaches the read-exit control carrying the data read from that configuration, with both buffers holding the binary input-position digits. It does so within the stated time bound, avoids both verdict states before the final time, and keeps every work-tape head within the stated radius.

**Proof.** The proof joins two runs. First, the prefix run reads the state and input-position fields, copies the position digits into the two buffers, and reaches the position-skip snapshot from which field reading begins. The field-reading run then reaches the specified read-exit snapshot carrying the state, position information, work-tape symbols and boundary marks, and tag. The equation identifying the zero-tape-read data with the initial data record lets these endpoints match; concatenating the runs preserves verdict avoidance and the head-radius bound (`recordRun_trans`).

For the time estimate, the joined record has $k+3$ fields (`cfgRecord_length`). The input-position field lies within the joined record: its offset plus its length is at most the total length (`fieldOffset_add_length_le`). This bounds the extra prefix and buffer-copy cost by $6$ times the digit-field length plus $17$, which is at most $17(L+1)$. The field-reading run costs at most $10(k+3)(L+1)$. Adding these bounds gives $(10(k+3)+17)(L+1)$, as claimed.

**Key facts.** `Turing.recordStep_read_prefix`, `Turing.recordStep_read_fields`, `Turing.recordRun_trans`, `Turing.fieldOffset_add_length_le`, `Turing.cfgRecord_length`.
