<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Examples.lean :: Complexity.evenScanTM_decidesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running time of the parity scan

**Claim.** For each Boolean input $x$, the even-parity scan machine halts after exactly $|x|+1$ steps and outputs the indicator of whether $x$ contains an even number of true bits.

**Proof.** After $|x|$ steps, the prefix invariant says the machine is in the state recording the parity of all of $x$, its head is positioned just beyond the input, and its output is still empty (`evenScanTM_prefix`). The input-symbol lemma identifies the symbol at that head position as the end marker (`Turing.FinTM.inputSymbol_at`). One further transition therefore applies the machine's end-marker action: it halts and appends the recorded parity bit. The iterate successor identity identifies this configuration with the run after $|x|+1$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The time-computation characterization then gives a computation at that exact time from the halting state and the required output (`Turing.FinTM.computesInTime_iff`). The parity recorded in the state is exactly the indicator of membership in the even-parity language.

**Key facts.** `Complexity.evenScanTM_prefix`, `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.computesInTime_iff`.
