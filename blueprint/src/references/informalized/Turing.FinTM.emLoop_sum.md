<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emLoop_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Successive Run Outputs

**Claim.** For a positive number of successive runs satisfying the stated time and output conditions, a run starting with output prefix $p$ halts within $NB$ steps and outputs $p$ followed by all the chunks in order.

**Proof.** Proceed by induction on $N$, generalizing the configuration and chunk sequences. The zero case is vacuous under the positivity hypothesis. For $N+1$, use the first segment's hypothesis to choose a time $a\le B$. Since the initial configuration has empty output, the output-prefix preservation law (`runFrom_output_prepend`) shows that starting instead with output $p$ gives the same first segment with output $p$ followed by the first chunk. If $N=0$, this segment is already the terminal halting segment, proving the result. Otherwise it reaches configuration $c_1$ with the first chunk appended. Apply the induction hypothesis to the shifted sequences, using prefix $p$ followed by that first chunk; all shifted configurations still have empty output and their segment bounds remain at most $B$. This gives a further time $b\le NB$ and the required halting output. The run-addition law (`runFrom_add`) combines the two times, whose sum is at most $(N+1)B$. The list decomposition of the range into its first index and the remaining indices identifies the accumulated chunks with the stated flattened concatenation.

**Key facts.** `Turing.MultiTapeTM.runFrom_output_prepend`, `Turing.MultiTapeTM.runFrom_add`.
