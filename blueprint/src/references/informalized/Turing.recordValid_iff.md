<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordValid_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing Valid Records

**Claim.** A list of fields is a valid record exactly when it has the prescribed length and field forms: a singleton state field, a bounded fixed-width binary position field, one window of tape cells with exactly one head mark for each work tape, and a singleton tag field.

**Proof.** For a valid record, take the input, configuration, and tag witnessing validity. The record construction immediately gives the required number of fields (`cfgRecord_length`), its first state field and final tag field. The input-position field is the binary digit list of the configuration's input head, whose value is at most $n+1$ because the head position is bounded by the input length. For each work tape, choose the cell contents from the configuration and choose the marked index to be the head position shifted by $s$. The head-window bound ensures this index lies among the $2s+1$ listed positions; translating equality of the head position into equality of indices gives precisely the required single-mark description.

Conversely, suppose the fields have the stated forms. Extract the state, bounded position value, tape-content functions and marked indices, and tag. Build a configuration on an input of length $n$ (the proof chooses the all-false input): use the extracted state and position, put the extracted tape contents in the window and blanks outside it, and place each head at its extracted marked index shifted by $s$. The bound on each marked index puts every head in the window, while the definition of the tapes makes every cell outside it blank. Comparing fields in order shows that the record of this configuration is the given list: the state and position fields agree by construction, each tape field agrees entry by entry, and the tag field agrees. The prescribed list length ensures there are no additional fields.

**Key facts.** `Turing.cfgRecord_length`.
