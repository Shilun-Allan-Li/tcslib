<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Map_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Finite-State Transduction

**Claim.** For a finite state set with decidable equality, a state update rule, an optional output rule for each state and input bit, and an optional final output rule, processing a word from any start state and appending the final output is polynomial-time computable.

**Proof.** Use the machine that scans the input from left to right, updates its finite control state according to the current bit, and appends the prescribed optional output bit at each step; when the input ends, it appends the prescribed final output and halts. The run characterization (`clA5Map_run`) proves by induction over the remaining input that, after processing any prefix, the machine's output is the output accumulated on that prefix followed by the recursively specified output of the remaining suffix. In particular, starting at the beginning with empty output and taking the whole word as the remaining suffix yields exactly `clA5MapWord` and a halting configuration after one more step than the input length. The initial configuration has the required form by the zero-work-tape extensionality fact (`Cfg.ext_zero_tapes`). Finally, the characterization of computation in time (`Turing.FinTM.computesInTime_iff`) turns this halting run and output equality into the machine's time bound; a linear bound is polynomial, as required.

**Key facts.** `Complexity.clA5Map_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`.
