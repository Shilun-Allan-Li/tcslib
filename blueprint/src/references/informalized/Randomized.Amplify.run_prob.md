<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.run_prob -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Probability in the Amplified Run

**Claim.** Under the stated halting and probability hypotheses, the output probability after a simulated run followed by its rewind equals the probability that the decision function applied to the initial counter plus the acceptance count across $i+1$ independent length-$T$ blocks returns $v$.

**Proof.** Apply the probability composition rule to separate the first $T$ choices, which simulate $N$, from the remaining amplified computation (`randProb_comp`). The step correspondence ensures that the amplified run follows the embedded run of $N$ (`step_emb`); after that run halts, its output determines the bumped counter and a rewind configuration (`rewindAt_emb`). By hypothesis, the suffix halts and its output probability is the induction value for that resulting counter. The counter update is $c$ if the run is not accepted and $c+1$ if it is accepted (`bump_val`). Thus the composition rule gives a mixture of the two suffix probabilities, weighted by the probabilities that the simulated run accepts or rejects. The acceptance bit agrees with the predicate that the output of $N$ is exactly $[\mathrm{true}]$ (`accBit_runWith`); the rejection probability is one minus the acceptance probability (`randProb_bool_false`). The resulting two-term recurrence is precisely the value for $i+1$ blocks (`val_succ`), proving the claim.

**Key facts.** `Randomized.Amplify.randProb_comp`, `Randomized.Amplify.step_emb`, `Randomized.Amplify.rewindAt_emb`, `Randomized.Amplify.bump_val`, `Randomized.Amplify.accBit_runWith`, `Randomized.randProb_bool_false`, `Randomized.Amplify.val_succ`, `Randomized.randProb_congr`.
