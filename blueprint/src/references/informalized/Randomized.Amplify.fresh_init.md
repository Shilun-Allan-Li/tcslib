<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.fresh_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fresh Initial Blocks

**Claim.** In the initial configuration of the amplified machine on $x$, every work tape in a block with positive block index is blank everywhere and has its head at cell $0$.

**Proof.** Fix a tape index whose block index is positive. The amplified machine’s initial configuration is the ordinary initial configuration: every work tape is blank at every cell and every work-tape head is at $0$. Thus both required properties hold for this tape.
