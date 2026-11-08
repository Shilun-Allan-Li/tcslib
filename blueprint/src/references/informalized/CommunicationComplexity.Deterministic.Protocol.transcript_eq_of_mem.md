<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.transcript_eq_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript determined by its input set

**Claim.** For a protocol transcript $t$, any input pair belonging to the input set associated with $t$ produces exactly $t$ when the protocol is run.

**Proof.** Proceed by induction on the protocol. At a terminal node the transcript is the unique empty transcript. At an Alice node, write $t$ as a Boolean message $b$ followed by a child transcript. Membership in the input set says both that Alice's message on the input equals $b$ and that the input belongs to the child's input set. Split on the two possible values of $b$: the first condition makes the actual run choose that same branch, and the induction hypothesis identifies its remaining transcript with the specified child transcript. Thus the full transcript is $t$. At a Bob node, membership gives the corresponding equality for Bob's message and membership in the child input set; the same two-branch argument and induction hypothesis yield the result.

**Caveat.** The supplied informal statement describes a rectangle and partition result, but the formal statement and proof establish that membership in a transcript's input set forces the run to produce that transcript. The account follows the formal statement and proof.
