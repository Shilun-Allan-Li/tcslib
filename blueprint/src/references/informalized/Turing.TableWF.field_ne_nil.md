<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.TableWF.field_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty fields in a well-formed table

**Claim.** If the header is nonempty and every field in every entry is nonempty, then every field of the table formed from the header and all entries is nonempty.

**Proof.** A field belonging to `tableFields h es` is either the header itself or belongs to the flattened list of entry fields. In the first case it is nonempty by the header hypothesis. In the second case, membership in a flattened list gives an entry containing that field; the well-formedness hypothesis for that entry says each of its fields is nonempty.
