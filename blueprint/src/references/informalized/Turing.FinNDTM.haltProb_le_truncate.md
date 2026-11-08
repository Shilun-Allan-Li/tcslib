<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltProb_le_truncate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncating the Halting-Output Probability

**Claim.** If the sum of nonhalting probabilities over every finite initial range is at most $B$, then at any length $t'$ the probability of halting with output $v$ is at most its probability at length $100B$ plus $1/100$.

**Proof.** The expected-time bound implies $1\le B$ (`Turing.FinNDTM.ExpTimeLe.one_le`), so $100B>0$. The halting result is prefix-stable (`Turing.FinNDTM.haltRun_isPrefixStable`), and for any prefix-stable result the probability of obtaining a specified value at an arbitrary length is at most its probability at length $t$ plus the nonhalting probability at length $t$ (`Randomized.randProb_eq_some_le`). Apply this with $t=100B$. The expected-time tail estimate for prefix-stable results gives nonhalting probability at that length at most $B/(100B)$ (`Randomized.notHaltedProb_le_div`). Since $B>0$, this ratio is $1/100$. Combining the two inequalities proves the claim.

**Key facts.** `Turing.FinNDTM.ExpTimeLe.one_le`, `Turing.FinNDTM.haltRun_isPrefixStable`, `Randomized.randProb_eq_some_le`, `Randomized.notHaltedProb_le_div`.
