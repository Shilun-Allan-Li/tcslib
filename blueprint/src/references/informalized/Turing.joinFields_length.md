<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.joinFields_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Joined Nonempty Fields

**Claim.** For a nonempty list of finite fields, the joined list has length equal to the sum of the field lengths plus the number of fields minus one.

**Proof.** First use the offset identity (`length_joinFields_add_one`): the joined length plus one equals the total field offset. Here the offset is the sum, over fields, of each field’s length plus one. A direct induction on the list of fields shows that this sum is the sum of the field lengths plus the number of fields. Substituting this expression into the offset identity and subtracting one gives the claimed formula.

**Key facts.** `Turing.length_joinFields_add_one`.
