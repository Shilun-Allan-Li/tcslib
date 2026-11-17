<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepFold_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Transduction

**Claim.** Processing a list with the rule that leaves the state and each symbol unchanged returns the initial state and the original list.

**Proof.** Induct on the list. The empty list returns the initial state and the empty output by definition. For a list with first symbol $a$, the rule leaves both the state and $a$ unchanged; applying the induction hypothesis to the remaining list therefore returns the initial state and the whole original list.
