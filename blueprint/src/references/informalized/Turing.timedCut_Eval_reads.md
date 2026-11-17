<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Eval_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reads of an Evaluation Configuration

**Claim.** The four work-tape symbols read in the evaluation configuration are the table-buffer symbol at the table cursor, the state-tape symbol at its cursor, and the two symbols read from the corresponding tapes of the base configuration.

**Proof.** A work-tape read is the tape content evaluated at that tape’s head position. In the evaluation configuration, the first two tapes are the table buffer and state tape, with head positions $p$ and $s$; their reads are therefore the buffer symbol at $p$ and $\sigma(s)$. The other two tape functions and head positions are inherited from the base configuration, so their reads agree with the base configuration’s reads on tapes 2 and 3. This covers all four tapes.
