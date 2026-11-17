<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.nonnegative_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Work Heads

**Claim.** If a finite Turing machine computes a function within time $T$, then it can be replaced by a machine over an enlarged finite alphabet with an injective symbol encoding, the same number of work tapes, nonnegative work-head positions throughout every initialized run, and runtime bounded by $T(n)+1$ on encoded inputs.

**Proof.** Choose the folded alphabet, its canonical symbol embedding, and the folded machine. The structural result `foldTM_nonnegative` says that every work head of this machine stays at a nonnegative position. The construction preserves the number of work tapes. To verify computation on an encoded input, fix a word $x$. The computation characterization `computesInTime_iff` gives that the original run halts with output $f(x)$ at time $T(|x|)$. The simulation result `foldCfg_run` identifies the folded machine's run after one additional step with the folded configuration of the original run. Therefore the folded run halts and outputs the symbolwise encoding of $f(x)$. The extra factor is $1$, so the resulting bound is $T(|x|)+1$.

**Key facts.** `Turing.FinTM.foldTM_nonnegative`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.foldCfg_run`.
