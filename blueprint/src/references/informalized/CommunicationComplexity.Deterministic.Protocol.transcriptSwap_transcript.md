<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.transcriptSwap_transcript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Role swap and transcript computation

**Claim.** Swapping the transcript produced by a protocol on $(x,y)$ gives the transcript produced by the role-swapped protocol on $(y,x)$.

**Proof.** Proceed by induction on the protocol. At a terminal node, both sides are the unique empty transcript. At an Alice node, the first message is computed from $x$; after swapping roles, the corresponding node is Bob's and computes that same message from the second coordinate of the reversed pair, also $x$. The protocols then continue in the same Boolean branch, where the induction hypothesis identifies the recursively transformed transcripts. At a Bob node the first message is computed from $y$, which is the first coordinate used by Alice at the swapped node on $(y,x)$; the same recursive argument applies.
