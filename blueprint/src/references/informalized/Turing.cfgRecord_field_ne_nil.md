<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.cfgRecord_field_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Configuration Record Fields

**Claim.** Every field in the record encoding of a configuration, with any tag, is a nonempty list.

**Proof.** The state field is a singleton, and the tag field is also a singleton, so both are nonempty. For the input-position field, its length is the width of the binary encoding, which is positive because that width is the bit length of the positive number $|x|+1$. Each work-tape field is indexed by the range of length $2s+1$, which is positive, so it too cannot be empty. These are all the possible fields in the record.
