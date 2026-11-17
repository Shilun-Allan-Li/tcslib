<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.transcriptComap_transcript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pull-back and transcript computation

**Claim.** For every pair of inputs in the new input spaces, pulling back the transcript of the original protocol on their mapped inputs gives exactly the transcript of the pulled-back protocol on the original pair.

**Proof.** Proceed by induction on the protocol. At a terminal node, both transcripts are the unique empty transcript. At an Alice node, the first message of the original run on the mapped inputs is the value of Alice's message function at the mapped Alice input. This is exactly the value of the pulled-back message function at the new Alice input. Both runs therefore choose the same Boolean branch, and the induction hypothesis identifies the pulled-back transcript of that child with the transcript computed there. At a Bob node the same argument uses Bob's mapped input and the induction hypothesis for the selected child.
