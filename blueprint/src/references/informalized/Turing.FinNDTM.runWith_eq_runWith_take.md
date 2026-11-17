<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.runWith_eq_runWith_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs stabilize after halting

**Claim.** If every choice word of length $t$ halts on input $x$, then any run driven by a word $w$ of length at least $t$ has the same final configuration as the run driven by the length-$t$ prefix of $w$.

**Proof.** Split $w$ into its prefix of length $t$ and its remaining suffix, so $w=(w.take\ t)++(w.drop\ t)$. The prefix has length $t$, and therefore the halting hypothesis says its run has halted state. The run-on-concatenation law says that running on $w$ is the same as first running on this prefix and then on the suffix (`runWith_append`). Once the prefix run has halted, further choices leave its configuration unchanged (`runWith_of_halt`). Thus the full run equals the run on the prefix.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
