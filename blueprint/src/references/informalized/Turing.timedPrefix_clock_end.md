<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_clock_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Delimiter Consumption

**Claim.** After $4|b_s|+4$ steps, the parser has consumed the clock delimiter and is in its first code-reading phase at position $4|b_s|+5$, with all of $b_s$ on its work tape and empty output.

**Proof.** First apply the partial clock-scan result at $j=|b_s|$. The work tape then contains $b_s$, the parser is in its first clock-reading phase, and the head is at position $4|b_s|+1$. The four positions following the repeated clock bits contain the delimiter pattern $0,0,1,1$ (`Turing.timed_clock_separator`). Apply the parser-advance lemma (`Turing.timedPrefix_advance`) successively at these positions: the first two transitions move through the clock-reading phases, and the next two consume the delimiter and enter the first code-reading phase. Each transition moves the head one position right, leaves the work tape unchanged, and emits nothing. Hence the final position is $4|b_s|+5$, with work tape $b_s$ and empty output. The input-length formula (`Turing.timed_input_length`) supplies the bounds for these positions.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedPrefix_advance`, `Turing.timedPrefix_clock`, `Turing.timed_clock_separator`, `Turing.timed_input_length`.
