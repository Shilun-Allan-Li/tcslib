<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.good_emb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound Under Embedding

**Claim.** Under the stated space bound for $N$, embedding its run on any choice word into block $j$ of $D$ preserves the bound $S$ on every work-tape head’s distance from cell $0$.

**Proof.** Fix a tape index in the amplified configuration. If it belongs to block $j$, its head position in the embedding is the corresponding head position in the run of $N$. The space bound for that run implies that the absolute value of this position is at most $S$: this is the consequence of the space estimate supplied by `abs_workTapePos_le`. If the tape belongs to another block, the embedding leaves its head position equal to the one in $D$, where the bound follows from the assumption that $D$ is good. These cases establish the required bound for every tape.

**Key facts.** `Randomized.Amplify.abs_workTapePos_le`.
