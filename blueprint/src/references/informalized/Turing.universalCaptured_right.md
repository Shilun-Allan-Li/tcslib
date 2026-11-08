<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalCaptured_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-Block Form of the Capture Endpoint

**Claim.** The interpreter-entry configuration of the output-capture wrapper is the right-block embedding of the four-tape configuration with initial interpreter state, the captured output in its first tape, three blank tapes, the specified head positions, and empty output; the original tapes and heads occupy the left block.

**Proof.** Compare the configuration fields. The states agree because the captured state is interpreter entry, and the input positions and outputs agree by their definitions. For the work tapes and head positions, split the index into the left block and the four-tape right block. On the left, both sides retain the source tapes and heads. On the right, split into the four possible indices: the first tape is the output buffer with its head at the output length, and the other three tapes are blank with heads at zero. These cases establish equality of both indexed fields, hence of the configurations.
