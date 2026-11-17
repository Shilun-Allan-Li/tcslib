<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.rewind_prob -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Probability During Rewind

**Claim.** Under the halting and freshness assumptions, when $c\le j+1$, the probability that a uniformly chosen choice word of length $i(T+|x|+2)+1$ produces output $[v]$ equals the probability that the decision function applied to $c$ plus the number of accepted length-$T$ blocks among $i$ uniformly random blocks returns $v$.

**Proof.** Induct on $i$. When $i=0$, the index is final, so either first choice and every remaining choice produce the same finished configuration, whose output is $[\mathrm{dec}(c)]$ because $C$ has empty output (`rewind_last`). The probability is therefore $1$ or $0$ according as this value equals $v$, which is exactly the zero-block value (`val_zero`). For the successor step, rewind to the next run index and restart there; freshness and empty output identify that restart with an embedding of the initial configuration (`restart_eq_emb`). The rewind segment has a fixed length depending on the input-head position, so splitting a uniformly random word after that segment transfers the output probability to the restarted run (`randProb_runWith_seg`). The simulated run halts within $T$ choices, and the induction hypothesis guarantees halting during the remaining rewind; consequently the added choices do not affect the output probability (`randProb_runWith_mono`). The run-probability decomposition (`run_prob`) then identifies this probability with the one obtained by adding the acceptance count from one new length-$T$ block. The counter bound needed for that decomposition follows from $c\le j+1$, and the resulting expression is exactly the successor value.

**Key facts.** `Randomized.Amplify.rewind_last`, `Randomized.Amplify.val_zero`, `Randomized.Amplify.rewind_run`, `Randomized.Amplify.restart_eq_emb`, `Randomized.Amplify.rewind_halts`, `Randomized.Amplify.run_halts`, `Complexity.LogProg.randProb_runWith_seg`, `Complexity.LogProg.randProb_runWith_mono`, `Randomized.Amplify.run_prob`.
