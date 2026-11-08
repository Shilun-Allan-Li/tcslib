<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.restoreFinalTrueProofValue_omit_proof -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring the Final Proof Value

**Claim.** For a Boolean word $w$ of length $m+2$, a proof word $q$ of length $m$, and a position $k$ in the proof word extended by a final true value, omitting that final position from the query, reading the resulting query on the input formed from $w$ and $q$, and restoring the omitted value returns the value at position $k$ of the extended proof word.

**Proof.** Split according to whether $k$ is the final position. If it is, omitting it produces no query value, while restoration supplies `true`; this is exactly the final value of the extended proof word. Otherwise, the query remains at the corresponding position of the original proof word. Reading it from the combined input returns that proof bit, and restoration leaves this value unchanged. Thus in either case the result is the value of the extended proof word at $k$.
