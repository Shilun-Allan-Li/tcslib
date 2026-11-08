<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RPExpected.lean :: Randomized.RP_PTM_subset_RP_ExpPTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Lies in Expected Time

**Claim.** Every language decidable in polynomial time by a one-sided randomized machine with acceptance probability at least $2/3$ on members belongs to the expected-time class with approximate member acceptance and no accepting halted branch on nonmembers.

**Proof.** Choose a polynomial-time exponent, constant, and machine witnessing membership, and fix an input. Let $T$ be its time bound. Since every random string of length $T$ halts, the cumulative nonhalting-probability bound follows from the halting-to-expected-time fact (Turing.FinNDTM.expTimeLe_of_haltsWithin). On a member input, a length-$T$ run halts, so the probability that the machine halts with output true equals its usual probability of outputting true (Randomized.randProb_congr and Turing.FinNDTM.haltRun_eq_some_iff). The original $2/3$ acceptance guarantee therefore implies the required $2/3-\varepsilon$ lower bound, taking the witnessing time to be $T$. On a nonmember, consider any halted run on a random string $w$. Its output is false by the original one-sided condition. Extend $w$ with false bits to a string $u$ of length at least $T$. Prefix stability of halted runs ensures that this extension has halted with the same output (Turing.FinNDTM.haltRun_isPrefixStable). Because the machine halts on every length-$T$ string, its behavior on $u$ agrees with its behavior on the first $T$ bits (Turing.FinNDTM.runWith_eq_runWith_take). Those first $T$ bits have length $T$, so the original nonmember condition forces their output, and hence the output on $u$ and on $w$, to be false. This establishes the required no-acceptance condition and completes the witness for the expected-time class.

**Key facts.** `Turing.FinNDTM.expTimeLe_of_haltsWithin`, `Randomized.randProb_congr`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.FinNDTM.haltRun_isPrefixStable`, `Turing.FinNDTM.runWith_eq_runWith_take`.
