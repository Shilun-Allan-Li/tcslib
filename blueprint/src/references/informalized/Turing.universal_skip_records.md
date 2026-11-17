<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_skip_records -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Skip of a List of Records

**Claim.** For a list of records of length $m+1$, skipping their concatenated bits from the fixed-field phase with remaining count $m$ reaches the continuation for the destination, with the table cursor advanced by the total bit length and the state tape and cursor unchanged.

**Proof.** Induct on the list of actions. The empty case is impossible because the length hypothesis says the list has length one more than a natural number. For a nonempty list, apply the one-record skipping result to its first action. The remaining-record count now matches the length of the tail. If the tail is empty, that count is zero and the one-record result already reaches the destination continuation. Otherwise the count is positive; apply the induction hypothesis to the tail, with the table prefix extended by the first record's bits. The run-addition law composes the first-record run and the tail run, yielding the cursor advance by the concatenated record length (`Turing.MultiTapeTM.runFrom_add`, `Turing.universal_skip_record`).

**Key facts.** `Turing.universal_skip_record`, `Turing.MultiTapeTM.runFrom_add`.
