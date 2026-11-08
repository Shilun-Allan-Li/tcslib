<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.restart_eq_emb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restart Configuration Embedding

**Claim.** When block $j$ is blank with all heads at cell zero and the output is empty, restarting the amplified configuration at run $j$ with counter $c$ equals embedding $N$’s initial configuration at that run and counter.

**Proof.** Compare the two configurations field by field. Their states agree: restarting sets the state to the run phase at $j$ with initial state, empty output summary, and counter $c$, which is exactly the embedding of the initial configuration. Their input-head positions also agree, since embedding uses the initial configuration’s input-head position, which is the restart position. For each tape coordinate, if its block is $j$, the hypothesis says that the existing tape is blank and its head is at zero, matching the initial configuration placed there by the embedding. If its block is not $j$, the embedding retains the tape and head position from the restarted configuration. Finally, both outputs are empty.
