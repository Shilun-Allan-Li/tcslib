<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.BPP_PTM_subset_BPP_ExpPTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Implies Polynomial Expected Time

**Claim.** Every language decidable by a bounded-error randomized Turing machine in polynomial time is decidable by a bounded-error randomized Turing machine whose expected running time is bounded by a polynomial.

**Proof.** Choose an exponent, constant, and machine witnessing membership in polynomial randomized time. On each input, the machine halts for every random string of the prescribed length, and its probability of producing the correct indicator is at least $2/3$. The halting bound implies the expected-time bound at that same time limit (the expected-time estimate for machines that halt within a fixed bound, `Turing.FinNDTM.expTimeLe_of_haltsWithin`). For the accuracy condition, take the expected-time definition's time parameter to be the original time bound. Since the machine halts on every random string of that length, the event that its halting run produces the correct output agrees, for all random strings, with the event that its output has that value. Thus their probabilities are equal (`Randomized.randProb_congr`, using `Turing.FinNDTM.haltRun_eq_some_iff` and the halting hypothesis), and the original $2/3$ correctness guarantee implies the required bound $2/3-\varepsilon$ for every positive $\varepsilon$. The same polynomial bound and machine therefore witness membership in the expected-time class.

**Key facts.** `Turing.FinNDTM.expTimeLe_of_haltsWithin`, `Randomized.randProb_congr`, `Turing.FinNDTM.haltRun_eq_some_iff`.
