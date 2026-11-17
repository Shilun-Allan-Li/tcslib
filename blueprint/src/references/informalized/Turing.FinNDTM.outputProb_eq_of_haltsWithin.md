<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.outputProb_eq_of_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output probability after guaranteed halting

**Claim.** If every choice word of length $t$ halts, then for every $t'\ge t$ and output word $v$, the probability of outputting $v$ after $t'$ choices equals the probability after $t$ choices.

**Proof.** Write the length-$t'$ random choice word as a word whose first $t$ bits are retained and whose remaining bits are discarded. The probability of an output event depending on this prefix is unchanged by sampling the longer word (`Randomized.randProb_take`), so it remains to compare the output on a word of length $t'$ with the output on its length-$t$ prefix. Every word of length at least $t$ has a halted run after its first $t$ choices, by the hypothesis that all length-$t$ runs halt. A halted configuration is unaffected by later choices, so the full run equals the run on the prefix (`Turing.FinNDTM.runWith_eq_runWith_take`). Consequently the two runs have the same output, and their output events agree for each sampled word; the probability is unchanged (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_take`, `Turing.FinNDTM.runWith_eq_runWith_take`, `Randomized.randProb_congr`.
