<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.runVal_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Value at Zero Blocks

**Claim.** Let $N$ be a finite-state nondeterministic Turing machine over Boolean symbols, let $x$ be a Boolean input, and let $K,c$ be nonnegative integers. With zero blocks, the run value starting at count $c$ is $1$ if the decision rule applied to $c$ returns true, and is $0$ otherwise.

**Proof.** When the number of blocks is zero, the block count is zero for every choice word, so the event defining the run value is constant: it holds exactly when the decision rule applied to $c$ is true. Since the choice-word length is also zero, the probability of this constant event is $1$ when it holds and $0$ otherwise (`Randomized.randProb_const`). The two constant predicates agree pointwise, and hence have equal probabilities (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_const`, `Randomized.randProb_congr`.
