<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/WindowClock.lean :: Turing.windowRun_summary_of_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary of a Halting Window Run

**Claim.** If the finite-state machine halts on input $x$ after $t$ steps with output $w$, uses at most $s$ units of space, and $t<N$, then the windowed run with radius $s$ and clock $N$, initialized with the empty summary, halts at the configuration reached after $t$ steps and returns the code for the summary of $w$.

**Proof.** First, the time-computation characterization (`FinTM.computesInTime_iff`) gives both that the configuration at time $t$ is halted and that its output is $w$. The space bound implies that all configurations through time $t$ lie in the radius-$s$ window (`FinTM.inWindow_of_spaceUsed_le`). Apply the halted-run result with accumulator $\sigma(u)=\mathrm{outSummaryCode}(\mathrm{outSummary}(u))$ and update rule $\mathrm{summaryTag}$. The accumulator compatibility needed there is exactly the fact that appending an optional Boolean to a word updates its summary code by the tag rule (`summaryTag_append`). This gives a halted window run whose final accumulator is the summary code of the machine's time-$t$ output. Replacing that output by $w$ using the computation characterization proves the stated result.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.inWindow_of_spaceUsed_le`, `Turing.summaryTag_append`, `Turing.windowRun_halted_of_run`.
