<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Prefix Parsing

**Claim.** After $4|b_s|+2|\alpha|+6$ steps, the parser is halted at position $4|b_s|+2|\alpha|+7$, with $b_s$ on its work tape and output $\alpha$.

**Proof.** Apply the partial code-scan result at $j=|\alpha|$. The parser is in its first code-reading phase, its work tape contains $b_s$, its output is all of $\alpha$, and its head is at position $4|b_s|+4+2|\alpha|+1$. The two positions following the code contain the delimiter bits $0,1$ (`Turing.timed_pair_separator`), as transferred to the nested encoding by the code-offset fact (`Turing.timed_code_get`). Apply the parser-advance lemma (`Turing.timedPrefix_advance`) at these two positions: it first enters the second code-reading phase and then halts, with no further output or work-tape change. The head advances twice, yielding position $4|b_s|+2|\alpha|+7$. The input-length formula (`Turing.timed_input_length`) ensures the delimiter positions are valid.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedPrefix_advance`, `Turing.timedPrefix_code`, `Turing.timed_code_get`, `Turing.timed_input_length`, `Turing.timed_pair_separator`.
