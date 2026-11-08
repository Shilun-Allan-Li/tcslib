<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_skip_records -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping a List of Records

**Claim.** When the list of actions has length one more than the skip counter and the table contains their serialized records, skipping from the prefix cursor for exactly the total record length reaches the continuation specified by the destination, with the cursor just past the records and the state tape unchanged.

**Proof.** Induct on the action list, generalizing the prefix and counter. The empty list is impossible under the length hypothesis, since its length cannot be one more than a natural counter. For a nonempty list $a::A$, that hypothesis identifies the counter value with $|A|$. Apply the one-record skipping result (`Turing.timedCut_skip_record`) to $a$. It advances past the first record and leaves the interpreter either in the destination continuation if $A$ is empty, or in fixed-field skipping with counter $|A|$ otherwise. In the latter case, apply the induction hypothesis to $A$, using the old prefix extended by the record for $a$. The table decomposition has exactly the required form for that extended prefix. Finally, the run-composition law (`Turing.MultiTapeTM.runFrom_add`) combines the first run and the run over $A$; list-length and cursor arithmetic identify the total number of steps and final cursor. Since each component run leaves the state tape and its cursor unchanged, so does the combined run.

**Key facts.** `Turing.timedCut_skip_record`, `Turing.MultiTapeTM.runFrom_add`.
