<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadActionK_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Transition Action

**Claim.** Reading the serialization of any action followed by a Boolean string returns that action and the unchanged suffix.

**Proof.** Write the action in its four components: input-head movement, work-tape data, output, and successor state. The serialized input is the concatenation of their encodings, followed by the suffix. The sign decoder recovers the input-head movement and leaves the rest intact. For the work tapes, each encoded write-and-movement pair is decoded by the work decoder; the vector-decoding append theorem then recovers the entire indexed family and preserves the suffix. The output decoder and successor-state decoder likewise recover their encoded values and leave the remaining suffix unchanged. Combining these componentwise decoding equations through the sequential reader gives the original action together with the original suffix.

**Key facts.** `Turing.codeReadSign_append`, `Turing.codeReadWork_append`, `Turing.codeReadVec_append`, `Turing.codeReadOutput_append`, `Turing.codeReadState_append`.
