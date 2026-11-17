<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.mem_DTIMEAdvice_one_of_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advice Complexity for Sublanguages of All Ones

**Claim.** If every word in $L$ consists entirely of ones, then $L$ has a decider using one advice bit at each input length and linear running time.

**Proof.** At length $n$, use as the single advice bit $b$ whether the all-ones word of length $n$ belongs to $L$. The machine scans the input and accepts precisely when every input bit is one and $b$ is true. The scan behavior is supplied by `Complexity.ao_scan`, and it takes a linear number of steps in the encoded input length. To see that this criterion decides $L$, a word belongs to the all-ones language exactly when it is the length-$n$ all-ones word (`Language.mem_allOnes_iff`). Since $L$ is contained in that language, membership in $L$ is equivalent to being all ones and having the advice bit true; the advice bit's definition gives exactly this equivalence. The machine's initial configuration agrees with the scan's prescribed starting configuration by zero-tape extensionality (`Turing.Cfg.ext_zero_tapes`). Its computation thus outputs the correct indicator. The scan bound is at most a constant multiple of $n+1$, as required; extending a computation to a larger time bound is valid by monotonicity (`Turing.FinTM.ComputesInTime.mono`), and the state/output characterization of computation supplies the advice-decider condition (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Complexity.ao_scan`, `Language.mem_allOnes_iff`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`.
