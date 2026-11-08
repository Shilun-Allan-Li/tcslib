<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.run_eq_transcript_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution agrees with transcript output

**Claim.** Running a protocol on an input pair gives the same value as reading the output attached to the transcript produced by that execution.

**Proof.** Proceed by recursion on the protocol. At an output node, the run and the transcript output are both the value attached to that node. At an Alice node, the execution follows the branch selected by Alice's input; the transcript records that same branch and then the transcript of the selected subprotocol. Applying the recursive result to that subprotocol identifies its run with the output recorded in the remainder of the transcript. At a Bob node the same reasoning applies to the branch selected by Bob's input.
