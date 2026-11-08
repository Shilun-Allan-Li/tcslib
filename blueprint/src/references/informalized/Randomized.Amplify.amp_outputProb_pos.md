<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.Amplify.amp_outputProb_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Probability with Positive Amplification

**Claim.** If every length-$t$ run of $N$ on $x$ halts, then the amplified machine's probability of outputting $[v]$ after $t+r(2t+3)+1$ steps equals the probability that applying $\mathrm{dec}$ to the number of accepted length-$t$ blocks in a uniformly chosen Boolean word of length $(r+1)t$ gives $v$.

**Proof.** The general output-probability formula `amp_outputProb` gives this probability at time $t+r(t+|x|+2)+1$. The machine also halts by that time (`amp_haltsWithin`), and by the positive-parameter halting bound (`amp_haltsWithin_pos`) it halts by time $t+r(2t+3)+1$. Output probability is unchanged when the observation time is increased beyond a halting bound (`outputProb_eq_of_haltsWithin`). Apply this invariance to compare both time parameters with the general formula; the two bounds show that the desired probability is the same as the formula's probability.

**Key facts.** `Randomized.Amplify.amp_outputProb`, `Randomized.Amplify.amp_haltsWithin_pos`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Randomized.Amplify.amp_haltsWithin`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`.
