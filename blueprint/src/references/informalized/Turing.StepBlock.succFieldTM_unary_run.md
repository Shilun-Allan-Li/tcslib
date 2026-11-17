<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_unary_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through a Unary State Field

**Claim.** Starting in the unary phase with `s` true bits followed by a false bit at the source head, after any `r ≤ s+1` steps the machine has scanned the first `r` bits, copying them to the destination exactly when copying is enabled. It remains unary through `r=s` and is done with live flag true after the final bit.

**Proof.** Induct on the number `r` of steps. At zero, the configuration has the original tapes and head positions, with unary control; this is the stated configuration with an empty copied prefix. For the successor step, the induction hypothesis identifies the current configuration with the one after scanning `r` bits. The bound on the total run ensures the next source symbol exists. The one-step transition description (`succFieldTM_unary_step`) advances the source head, writes that symbol to the destination precisely when copying is enabled, and advances the destination head in that case. It therefore extends the copied prefix from length `r` to `r+1`. If the current symbol is true, the machine stays unary; if it is false, which here is the final bit of the given word, it enters done with true live flag. Since the word consists of `s` ones followed by that false bit, these alternatives are exactly unary for `r+1 ≤ s` and done at `r+1=s+1`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.StepBlock.succFieldTM_unary_step`.
