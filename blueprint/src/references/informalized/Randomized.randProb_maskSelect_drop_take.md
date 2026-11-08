<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.randProb_maskSelect_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Under Masked Segment Selection

**Claim.** If $s+|\mathrm{mask}|\le m$, selecting from the segment of a uniformly random Boolean word of length $m$ immediately after its first $s$ bits, and retaining the positions marked true by the mask, satisfies a predicate with the same probability as a uniformly random word whose length is the number of true mask entries.

**Proof.** First, the substring obtained by dropping the initial $s$ bits and taking the next $|\mathrm{mask}|$ bits is uniformly distributed as a Boolean word of length $|\mathrm{mask}|$; the condition $s+|\mathrm{mask}|\le m$ ensures this segment is present (`Randomized.randProb_drop_take`). Applying the mask to that substring preserves the probability of the predicate exactly as if one had started with a uniform word whose length is the number of true mask entries (`Randomized.randProb_maskSelect`). Combining these two equalities proves the claim.

**Key facts.** `Randomized.randProb_drop_take`, `Randomized.randProb_maskSelect`.
