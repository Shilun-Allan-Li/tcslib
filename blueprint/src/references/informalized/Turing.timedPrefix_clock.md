<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_clock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Extraction After a Partial Scan

**Claim.** For each $j\le |b_s|$, after $4j$ steps the parser is in its first clock-reading phase at position $4j+1$, with the prefix of $b_s$ of length $j$ on its work tape and no output.

**Proof.** Induct on $j$. At $j=0$, the initial configuration has the claimed state, head position, empty work tape, and empty output. For the successor case, $j<|b_s|$, so the next bit $b_s[j]$ exists. The encoding repeats this bit in four consecutive positions, as given by `Turing.timed_clock_get`. Starting from the induction hypothesis, apply the parser-advance lemma (`Turing.timedPrefix_advance`) four times: the first three transitions move through the successive clock-reading phases, and the fourth writes $b_s[j]$ to the clock work tape and returns to the first phase. The input head advances by four positions and the output remains empty. Finally, the list identity $\operatorname{take}(j,b_s)\mathbin{+0}[b_s[j]]=\operatorname{take}(j+1,b_s)$ identifies the updated work tape with the required prefix. The stated input-length formula (`Turing.timed_input_length`) ensures these positions lie within the encoded input.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedPrefix_advance`, `Turing.timed_clock_get`, `Turing.timed_input_length`.
