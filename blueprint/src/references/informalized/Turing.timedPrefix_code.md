<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code Extraction After a Partial Scan

**Claim.** For each $j\le |\alpha|$, after $4|b_s|+4+2j$ steps the parser is in its first code-reading phase at position $4|b_s|+4+2j+1$, with $b_s$ on its work tape and the prefix of $\alpha$ of length $j$ in its output.

**Proof.** Induct on $j$. The case $j=0$ is the clock-delimiter result (`Turing.timedPrefix_clock_end`), since the output prefix is empty. For the successor case, $j<|\alpha|$. The nested encoding places two copies of $\alpha[j]$ consecutively at the corresponding code positions: the pair-position fact `Turing.timed_pair_get`, together with the offset identity `Turing.timed_code_get`, identifies the two bits read. From the induction hypothesis, apply the parser-advance lemma (`Turing.timedPrefix_advance`) twice. The first transition enters the second code-reading phase without emitting output; the second returns to the first phase and emits $\alpha[j]$. The work tape remains $b_s$, the input head advances by two, and the output grows by that bit. The list identity adjoining $\alpha[j]$ to its length-$j$ prefix gives the length-$(j+1)$ prefix. The input-length formula (`Turing.timed_input_length`) justifies the position bounds.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedPrefix_advance`, `Turing.timedPrefix_clock_end`, `Turing.timed_code_get`, `Turing.timed_input_length`, `Turing.timed_pair_get`.
