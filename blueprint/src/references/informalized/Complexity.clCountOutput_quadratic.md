<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountOutput_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Bound for Movement Counts

**Claim.** The specified count-output machine halts on the packed input with output equal to the little-endian binary representation of the $i$th movement count after $T$ steps, and its space usage at the stated quadratic time bound is a natural number.

**Proof.** Let $x$ be the packed input and let $W$ be its length. Each input field has length at most $W$, by the width bound for fields in the encoding (`clFields_width`). In particular, the clock field has length $T$, so $T\le W$. The recording-machine completeness result supplies a time $a$ bounded by $2W+4+k(3W+7)+(4l+7)(T+1)^2$ at which the record machine reaches the configuration containing the full run data and movement counts (`clRecord_complete`). The selected tape is precisely the one containing the $i$th recorded count; this is the placement’s defining property, used here only to identify the tape. The output-machine correctness result then shows that the output machine, starting from that recorded configuration, outputs the selected word in $a+j+|w|+4$ steps, where $j$ is the selected head position (`clOutputAt_compute`). Its hypotheses hold: the recording machine has not yet produced output, its return state is not its initial state, and that return state is idle (`clRecord_idle`). The bound on each movement count gives the needed bound on $j$; and the elapsed-time width bound gives $|w|\le T$ (`clCounts_bound`, `clElapsed_width`). Finally, the size-budget inequality bounds the total time by the displayed quadratic expression (`clCount_size_budget`). Monotonicity of computation in the time allowance extends the computation to exactly that bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Complexity.clFields_width`, `Complexity.clRecord_complete`, `Complexity.clOutputAt_compute`, `Complexity.clRecord_idle`, `Complexity.clCounts_bound`, `Complexity.clElapsed_width`, `Complexity.clCount_size_budget`, `Turing.FinTM.ComputesInTime.mono`.
