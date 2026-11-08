<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.runVal_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Run-Value Recurrence

**Claim.** The run value for $i+1$ blocks from count $c$ is $p$ times the run value for $i$ blocks from count $c+1$, plus $1-p$ times the run value for $i$ blocks from count $c$, where $p$ is the acceptance probability on a uniformly random length-$K$ choice word.

**Proof.** Split a uniformly random choice word of length $(i+1)K$ into its first block of length $K$ and the remaining $iK$ bits. The block-count successor identity expresses the total count as the count in the tail plus one exactly when the first block accepts. Accordingly, acceptance of the final decision rule is the disjoint union of two events: the first block accepts and the tail succeeds starting from count $c+1$, or the first block rejects and the tail succeeds starting from count $c$. Disjointness follows because the first block cannot both accept and reject. The probability of each event factors into the probability for its first-block condition times the probability for its tail condition, by the split rule for independent uniform prefixes and suffixes. The first-block acceptance probability is $p$, and its rejection probability is $1-p$. Adding the two disjoint contributions gives the recurrence.

**Key facts.** `Randomized.randProb_congr`, `Randomized.blockCount_succ`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_split`, `Randomized.randProb_bool_false`.
