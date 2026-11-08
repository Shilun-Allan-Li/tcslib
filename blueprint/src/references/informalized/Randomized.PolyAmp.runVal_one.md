<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.runVal_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability Across Trials

**Claim.** With the one-sided decision rule, $K$ trials per block, $K+1$ blocks, and initial count zero, the run value is $1-(1-p)^{K+1}$, where $p$ is the acceptance probability for a uniformly random length-$K$ choice word.

**Proof.** The block-count distribution formula with $K+1$ blocks and count zero says that the probability of no accepting block is $(1-p)^{K+1}$: the binomial coefficient for choosing zero successful blocks is one. The one-sided rule accepts exactly when the count is positive. Hence the run value is the probability complementary to the event that the count is zero, namely $1-(1-p)^{K+1}$.

**Key facts.** `Randomized.randProb_blockCount`, `Randomized.randProb_not`, `Randomized.randProb_congr`.
