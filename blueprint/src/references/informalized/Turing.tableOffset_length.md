<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.tableOffset_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Complete Table Offset

**Claim.** The offset after all entries of the table formed from header $h$ and entries $es$ equals the length of the joined list of table fields plus one.

**Proof.** At the full length of $es$, taking the first $|es|$ entries leaves $es$ itself. The number of fields represented by the table offset is therefore one header field plus the total number of fields in the entries, which is the length of the table's field list. That list is nonempty because it begins with $h$. The offset of a nonempty list of fields through its full length equals the length of the joined fields plus one (`Turing.fieldOffset_length`), yielding the result.

**Key facts.** `Turing.fieldOffset_length`.
