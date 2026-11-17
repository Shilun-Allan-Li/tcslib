<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.val_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-block recurrence for acceptance value

**Claim.** The value for $i+1$ blocks and offset $c$ is the acceptance probability of one length-$T$ block times the $i$-block value with offset $c+1$, plus the probability of a nonaccepting first block times the $i$-block value with offset $c$.

**Proof.** Unfold the value as a probability over choice strings and split a string of length $(i+1)T=T+iT$ into its first $T$ bits and remaining $iT$ bits. The block-count recurrence (`Randomized.blockCount_succ`) says that the first block contributes one to the count precisely when it is accepted. Accordingly, the event defining the value is the disjoint union of two cases: the first block is accepted and the suffix satisfies the $i$-block condition with offset $c+1$, or the first block is not accepted and the suffix satisfies it with offset $c$. The two cases are disjoint because the first block cannot both accept and fail to accept. Probability is invariant under replacing an event by an equivalent one on all choice strings (`Randomized.randProb_congr`), and probabilities of disjoint unions add (`Randomized.randProb_or_disjoint`). Independence of the first and remaining bits factors each case into the corresponding product of probabilities (`Randomized.randProb_split`). Finally, the probability that the first block is nonaccepting is one minus its acceptance probability (`Randomized.randProb_bool_false`). Substituting these factors gives the claimed recurrence.

**Key facts.** `Randomized.blockCount_succ`, `Randomized.randProb_congr`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_split`, `Randomized.randProb_bool_false`.
