<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.inZPP_of_mem_ZPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected-time zero-error simulation

**Claim.** Every language in the stated expected-polynomial-time zero-error machine class has an efficient polynomial-witness zero-error verifier with abort probability at most $1/2$.

**Proof.** Choose the exponent and coefficient witnessing membership in the class, and let $B=c(|x|^e+1)$ be the expected-time bound. Run the nondeterministic machine with a choice tape of length $Q=4c(|x|+1)^e$. The choice-budget estimate (`Turing.choiceBudget_le`) ensures $2B\le Q$, so the truncation estimate applies and $Q>0$. The expected-time bound is at least one (`Turing.FinNDTM.ExpTimeLe.one_le`), and the truncation theorem (`Turing.FinNDTM.ZDecidesInTime.truncate`) gives probability at least $1-B/Q\ge1/2$ of halting with the correct output.

The bounded-halting simulation (`Randomized.exists_eff_haltRun`) produces an efficient verifier whose answer bit corresponds exactly to the simulated machine halting with that one-bit output. Every halting computation has the correct output, so this verifier never answers incorrectly. If it aborts, the machine did not halt with the correct output; hence its abort probability is at most the complement of the correct-output probability. The complement identity for uniform random tapes (`Randomized.randProb_not`) and the truncation bound yield an abort probability at most $1/2$.

**Key facts.** `Turing.choiceBudget_le`, `Turing.FinNDTM.ExpTimeLe.one_le`, `Turing.FinNDTM.ZDecidesInTime.truncate`, `Randomized.exists_eff_haltRun`, `Randomized.randProb_mono`, `Randomized.randProb_not`.
