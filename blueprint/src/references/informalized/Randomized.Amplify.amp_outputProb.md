<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.amp_outputProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Probability of the Amplified Machine

**Claim.** Assuming every length-$T$ run of $N$ on $x$ halts, the probability that the amplified machine outputs $[v]$ after $T+r(T+|x|+2)+1$ steps equals the probability that applying $\mathrm{dec}$ to the number of accepted length-$T$ blocks in a uniformly chosen Boolean word of length $(r+1)T$ gives $v$.

**Proof.** Unfold the definitions of output probability and output under a choice word. The amplified initial configuration is the embedding of the original initial configuration (`init_eq_emb`), and it is fresh (`fresh_init`). The probability analysis of the embedded simulation (`run_prob`) expresses the full run's output probability in terms of the outcomes of the successive original runs and the final rewind. Its hypotheses are provided by the halting guarantee for $N$, the rewind-halting bound (`rewind_halts`), and the rewind probability calculation (`rewind_prob`). That calculation identifies the final output with applying $\mathrm{dec}$ to the counter recording the accepted simulations. Rewriting each simulation outcome as acceptance on its corresponding block, and collecting the blocks into a word of length $(r+1)T$, yields the stated uniform probability.

**Key facts.** `Randomized.Amplify.init_eq_emb`, `Randomized.Amplify.fresh_init`, `Randomized.Amplify.rewind_halts`, `Randomized.Amplify.rewind_prob`, `Randomized.Amplify.run_prob`.
