<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.tableOffset_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Offset in a Table of Fields

**Claim.** For a header $h$ and a list $es$ of nonempty entries, the offset through the first $j$ entries is $|h|+1$ plus the sum, over those entries, of the length of their fields joined by single separators plus one separator per entry.

**Proof.** The table fields begin with the header, followed by all fields in the entries. The offset through this header and the fields in the first $j$ entries splits as the header contribution $|h|+1$ plus the offset through those entry fields (`Turing.fieldOffset_cons_succ`). Rewrite the first $j$ entries of the flattened list of fields as the flattening of the first $j$ entries themselves; distributing the sum over this flattening reduces the claim entry by entry. Each entry is nonempty, so its total field offset is the length of its fields joined by separators, plus one (`Turing.fieldOffset_length`). Summing these identities gives the stated formula.

**Key facts.** `Turing.fieldOffset_cons_succ`, `Turing.fieldOffset_length`.
