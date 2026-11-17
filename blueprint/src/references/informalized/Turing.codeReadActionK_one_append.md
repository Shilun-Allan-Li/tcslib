<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadActionK_one_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Action Decoding

**Claim.** Reading the serialization of a one-work-tape action followed by a Boolean string returns the action and the unchanged suffix.

**Proof.** The one-tape serialization agrees with the general action serialization when there is one work tape. Rewrite using this equality, then apply the general action-decoding theorem, which says that decoding the general serialization followed by any suffix returns the encoded action and that suffix.

**Key facts.** `Turing.actionBits_eq_actionBitsK`, `Turing.codeReadActionK_append`.
