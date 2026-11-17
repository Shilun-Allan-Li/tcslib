<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.init_eq_emb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration as an Embedding

**Claim.** The amplified machine’s initial configuration on $x$ equals the embedding of the initial configuration of $N$ into run $0$ with counter $0$, using that amplified initial configuration as the background.

**Proof.** Compare the configuration fields. The embedded state is the run phase with run index $0$, initial state of $N$, empty accumulated output, and counter $0$, which is exactly the amplified initial state. The input-head position and output also agree directly. For each tape, the block-$0$ case takes the corresponding tape contents and head position from $N$’s initial configuration; these are blank and at $0$, just as in the amplified initial configuration. Every other block retains the amplified initial tape contents and head position. Thus all fields agree.
