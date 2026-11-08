<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.notHaltedProb_repeatRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting Probability Under Repeated Runs

**Claim.** For $0<t$, $s<t$, and any natural number $m$, the probability that the repeated-run procedure has not halted on a uniformly random string of length $mt+s$ equals the $m$th power of the probability that one run of $q$ has not halted on a uniform length-$t$ string.

**Proof.** Proceed by induction on the number $m$ of complete blocks. When $m=0$, the input has length $s<t$, so the repeated-run procedure returns no output on every such input (`Randomized.repeatRun_of_lt`). Its nonhalting event is therefore certain, with probability one (`Randomized.randProb_true`), matching the zeroth power.

For the induction step, write the length $(m+1)t+s$ input as a first block of length $t$ followed by a string of length $mt+s$. The probability that both the first block fails to produce an output and the remaining input fails under the repeated-run procedure factors as the product of their probabilities (`Randomized.randProb_split`). Indeed, on an input long enough to contain the first block, the procedure runs $q$ on that block and then continues on the suffix (`Randomized.repeatRun_of_le`); it returns no output exactly when both runs return no output, by the characterization of when an option-valued result is none. The induction hypothesis identifies the suffix probability with the $m$th power of the one-block failure probability. Multiplying by the first block's failure probability gives the $(m+1)$st power. The event identifications preserve probability (`Randomized.randProb_congr`).

**Key facts.** `Randomized.repeatRun_of_lt`, `Randomized.randProb_true`, `Randomized.randProb_split`, `Randomized.repeatRun_of_le`, `Randomized.randProb_congr`.
