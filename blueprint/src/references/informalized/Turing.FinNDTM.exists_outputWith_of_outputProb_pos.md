<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.exists_outputWith_of_outputProb_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Probability Gives a Witness

**Claim.** If the fraction of length-$t$ choice words on which $N$ outputs $v$ is positive, then some length-$t$ choice word makes $N$ output exactly $v$.

**Proof.** Positive probability means the event that a uniformly chosen length-$t$ Boolean word produces $v$ has positive probability. The positive-probability witness theorem for finite Boolean choice spaces (`Randomized.exists_ofFn_of_randProb_pos`) therefore gives a function $r:\mathrm{Fin}(t)\to\mathrm{Bool}$ whose associated word satisfies the output condition. Take $w$ to be that word, `List.ofFn r`. Its length is $t$, and the witness condition says exactly that $N$ outputs $v$ on $w$.

**Key facts.** `Randomized.exists_ofFn_of_randProb_pos`.
