<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.unusedTape_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding an Unused Work Tape

**Claim.** If a machine with no work tapes computes a function in time $T$, then adding one unused work tape preserves that computation and time bound.

**Proof.** Fix an input $x$. The configuration embedding keeps the state, input-head position, and output, and assigns the added tape blank contents with its head at the origin. The one-step compatibility lemma (`unusedTape_step`) says that stepping the enlarged machine after this embedding gives the embedding of the original machine's next configuration. Iterating this compatibility for $T(|x|)$ steps, by the run-commutation theorem (`runFrom_comm_of_step`), identifies the enlarged run with the embedding of the original run. In particular, their states and outputs agree. The characterization of computation in time by halting state and output (`computesInTime_iff`) turns the original computation witness into the required witness for the enlarged machine; its space component is immaterial to this time-only specification.

**Key facts.** `Turing.FinTM.unusedTape_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.FinTM.computesInTime_iff`.
