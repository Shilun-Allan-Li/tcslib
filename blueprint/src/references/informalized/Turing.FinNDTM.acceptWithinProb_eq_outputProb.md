<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.FinNDTM.acceptWithinProb_eq_outputProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance and output probabilities

**Claim.** If every choice word of length $T$ halts and $T\le t$, then the probability of acceptance within $t$ steps equals the probability that a uniformly chosen length-$T$ choice word produces output $[\mathrm{true}]$.

**Proof.** First use the fact that once every length-$T$ run halts, extending the choice word to length $t$ does not change the output distribution (`outputProb_eq_of_haltsWithin`). Thus the acceptance probability at horizon $t$ can be compared with the output-$[\mathrm{true}]$ probability at horizon $T$. To make that comparison explicit, take any Boolean choice vector of length $t$ and view it as a word via `List.ofFn`. Every such length-$t$ run halts, since `HaltsWithin` extends from $T$ to $t$ (`HaltsWithin.mono`). For a halting run, acceptance within $t$ is precisely the condition that its output is $[\mathrm{true}]$; conversely, that output condition together with guaranteed halting gives acceptance. The two events therefore agree pointwise, so their uniform probabilities agree (`randProb_congr`).

**Key facts.** `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Turing.NDTM.HaltsWithin.mono`, `Randomized.randProb_congr`.
