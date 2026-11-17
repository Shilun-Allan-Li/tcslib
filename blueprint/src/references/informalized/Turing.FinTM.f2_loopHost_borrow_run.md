<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the borrow operation

**Claim.** For every prefix $v$, starting in phase 8 with counter contents $vw$ and head at $|v|$, after $b(w)+1$ steps the tape contains $v$ followed by the debited word, its head is at $|v|+b(w)-1$, and the machine is in phase 9 on carry or phase 10 otherwise, with the remaining specified frame data preserved.

**Proof.** Induct on the word $w$, proving the assertion for every prefix $v$. If $w$ is empty, the borrow-position function is zero and the single transition takes the machine to phase 10, leaving the prefix intact; this is the empty-word case of the transition calculation (`f2_loopHost_borrow_step`). If the first bit is true, the debit changes it to false and reports a carry, and one transition reaches phase 9 with the required tape and head position, again by that step calculation. If the first bit is false, the debit changes it to true and continues borrowing through the remaining suffix. The first transition writes that true bit, moves the head forward, and places the configuration in the form covered by the induction hypothesis with prefix $v$ extended by true. Applying the induction hypothesis to the suffix gives the desired debited word and final position; the definition of the borrow position and the run successor identity (`runFrom_succ_eq_step`) account for the extra initial step. List concatenation and integer-position arithmetic identify the resulting tape and head with the claimed ones.

**Key facts.** `Turing.FinTM.f2_loopHost_borrow_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
