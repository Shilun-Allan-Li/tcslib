<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.step_emb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step commutes with embedding

**Claim.** For a nonhalted configuration $u$ of $N$, stepping the amplified machine from its embedding at run index $j$ and counter $c$ gives the embedding of the one-step result of $N$, at the same index and counter.

**Proof.** Because $u$ is not halted, write its state as $q$. In the embedded configuration, the work tapes in block $j$ reproduce those of $u$: the block-index and within-block maps recover $j$ and each original tape index (`Randomized.Amplify.blk_mk`, `Randomized.Amplify.idx_mk`). The input symbol is also the same, and the embedded state is the run phase carrying $q$, the summary of $u$'s output, and $c$.

Thus the amplified step uses precisely the transition of $N$ on $q$ and the symbols seen by $u$. Its action is applied only to block $j$; every other block receives no write and no head movement. The output summary after appending the transition's optional output equals the combination of the previous summary with that output (`Randomized.Amplify.summ_append`). Comparing the resulting state, input position, work tapes and head positions, and output component gives exactly the embedding of the stepped configuration of $N$.

**Key facts.** `Randomized.Amplify.blk_mk`, `Randomized.Amplify.idx_mk`, `Randomized.Amplify.summ_append`.
