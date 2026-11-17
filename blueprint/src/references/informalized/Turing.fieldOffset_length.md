<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.fieldOffset_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total field offset

**Claim.** For a nonempty finite list of fields, the offset after all fields is the length of the joined list plus one.

**Proof.** The total-offset formula for joined fields (`Turing.length_joinFields_add_one`) states that the joined-list length plus one equals the offset after all fields. Reversing the two sides gives the result.

**Key facts.** `Turing.length_joinFields_add_one`.
