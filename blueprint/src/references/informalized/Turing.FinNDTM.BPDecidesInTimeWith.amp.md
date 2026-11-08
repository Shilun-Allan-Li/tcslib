<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Turing.FinNDTM.BPDecidesInTimeWith.amp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification of the Success Guarantee

**Claim.** Under the stated halting and success hypotheses, the specified majority amplification halts within $t(|x|)+2n(2t(|x|)+3)+1$ steps and achieves success probability at least $1-2(1-4\varepsilon^2)^n$ on every input.

**Proof.** Fix an input $x$ and write $T=t(|x|)$. The original machine halts on every branch within $T$ steps, by the halting component of the hypothesis. The amplified machine simulates $2n+1$ runs and uses the prescribed threshold to output the majority bit. The halting-time bound for this construction (\texttt{amp_haltsWithin_pos}) gives a bound of $T+(2n)(2T+3)+1$, since its parameter is $r=2n$. Its output distribution is identified by \texttt{amp_outputProb_pos} with the distribution of the threshold decision on the $2n+1$ simulated runs. Applying the majority probability bound (\texttt{majority_randProb_ge}) to the original success guarantee, with $v$ equal to the membership indicator, gives probability at least $1-2(1-4\varepsilon^2)^n$ of outputting that indicator. This holds for each $x$, as required.

**Key facts.** `Randomized.Amplify.amp_haltsWithin_pos`, `Randomized.Amplify.amp_outputProb_pos`, `Randomized.Amplify.majority_randProb_ge`.
