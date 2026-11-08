<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_copy_run_base -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base cases for copying joined fields

**Claim.** For $m\le 1$, the machine copies the joined fields within linear time, avoids its exit state beforehand, keeps both heads within a linear radius, and finishes with the specified tape contents.

**Proof.** Split on $m$. If $m=0$, the list of fields is empty. Choose time and constant zero: the machine’s entry state is already its exit state, and the empty target word leaves the tape contents unchanged. The only time at or before the chosen time is time zero, so the head bound is immediate; the configuration equality follows from the empty-field identities. If $m=1$, write the sole field as $u$. Its joined encoding has length $|u|$. The source-tape hypothesis identifies the recorded field with the usual buffer containing $u$ on offsets from $-1$ through $|u|$: the field-to-buffer identity (`fieldsTape_field`) supplies this identification. Apply the copying-run result (`copyTM_run_ofCfg`) to copy that buffer from tape 0 to tape 1. It gives completion after $2|u|+2$ steps, no earlier visit to the done state, and a head-radius bound throughout the run. Since the joined word has length $|u|$, the time is at most $2(|u|+1)$; taking $C=2$ also bounds each head’s displacement by $2(|u|+1)$. Finally, the copying result’s buffer on tape 1 is exactly the requested field encoding, again by `fieldsTape_field`; outside the destination interval, its tape-update description preserves the original contents.

**Key facts.** `Turing.fieldsTape_field`, `Turing.copyTM_run_ofCfg`.
