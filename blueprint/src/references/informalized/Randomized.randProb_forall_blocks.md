<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_forall_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Success in Every Block

**Claim.** For a uniformly random Boolean word of length $tL$, the probability that each of its $t$ consecutive blocks has a value satisfying $Q$ is the probability that a uniformly random Boolean word of length $L$ has value satisfying $Q$, raised to the $t$th power.

**Proof.** Proceed by induction on $t$. When $t=0$, the condition on every block is vacuous, so its probability is $1$, which is the zeroth power of the one-block probability. For the induction step, split a word of length $(t+1)L$ into its first $L$ bits and its remaining $tL$ bits. The condition on all blocks is equivalent to the conjunction of the condition on the first block and the condition on the remaining blocks. The probability of these two conditions factors as a product by the split rule for independent uniform substrings (`Randomized.randProb_split`). The induction hypothesis gives the remaining-block probability as the $t$th power of the one-block probability, so the product is its $(t+1)$st power. The identification of the first block with the initial segment and of later blocks with the corresponding blocks of the tail follows from the definition of block values.

**Key facts.** `Randomized.randProb_true`, `Randomized.randProb_split`.
