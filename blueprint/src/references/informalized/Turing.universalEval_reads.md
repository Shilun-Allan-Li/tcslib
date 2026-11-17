<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalEval_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reads in an Evaluation Configuration

**Claim.** In the evaluation configuration, the four work-tape reads are the buffer symbol at the table cursor, the state-tape symbol at its cursor, and the third and fourth reads of the base configuration.

**Proof.** Evaluate the work-tape read function at an arbitrary one of the four indices. The evaluation configuration assigns its tapes and head positions by the same four-way block decomposition. Splitting the index into $0,1,2,$ or $3$ shows respectively that the read is the table buffer at its cursor, the state tape at its cursor, or the corresponding base-configuration read on tape three or four. Therefore the read functions agree at every index.
