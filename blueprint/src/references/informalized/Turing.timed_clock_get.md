<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of the quadrupled clock word

**Claim.** For $j<|b_s|$ and $r<4$, the entry at index $4j+r$ of the nested pair encoding is $b_{s,j}$.

**Proof.** Rewrite the nested encoding using the input-layout identity (`timed_input_layout`), which presents it as the clock prefix for $b_s$ followed by the encoding of the remaining data. Induct on $b_s$. For the empty word the hypotheses are impossible. If $j=0$, the four possible values $r=0,1,2,3$ select the four copies of the head bit in the clock prefix, so each entry is the first bit. If $j$ is a successor, removing the prefix contributed by the first bit shifts the requested index by four; the induction hypothesis then identifies that entry with the corresponding bit of the tail. The index simplifications match this shifted position with $4j+r$.

**Key facts.** `Turing.timed_input_layout`.
