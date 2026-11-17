<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPrepare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact preparation run

**Claim.** From the initial configuration, after exactly $2(|s|+1)$ steps the preparation machine reaches phase $2$, with the candidate and scratch tapes, head positions, input position, and flag as stated.

**Proof.** First identify the initial configuration with the scan configuration at count zero: the candidate is on the first tape, the scratch tapes are blank, and the heads and input position have the prescribed initial values. The scan calculation (`splitPrepare_scan`) then gives the scan configuration at count $|s|$ after $|s|$ steps. One additional step reaches the ready configuration in phase $1$ with displacement $|s|-1$ (`splitPrepare_extra`). Thus the first $|s|+1$ steps end at precisely the starting configuration for the rewind calculation with $j=|s|$. Run for another $|s|+1$ steps and apply `splitPrepare_rewind`; the result is phase $2$ with zero head displacement. The two run segments combine to $2(|s|+1)$ steps, and the ready configuration carries the flag recording whether $|w|<|s|$.

**Key facts.** `Turing.FinTM.splitPrepare_scan`, `Turing.FinTM.splitPrepare_extra`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.splitPrepare_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
