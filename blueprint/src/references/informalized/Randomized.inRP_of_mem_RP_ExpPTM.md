<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RPExpected.lean :: Randomized.inRP_of_mem_RP_ExpPTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected-Time Randomized Recognition Implies RP

**Claim.** If a language has a finite nondeterministic machine with random choice bits satisfying the given polynomial expected-time and one-sided output conditions, then it belongs to RP in the polynomial-time verifier model.

**Proof.** Choose a machine and polynomial expected-time bound witnessing membership in the stated expected-time class. A fixed-length choice verifier captures whether a prescribed choice string makes the machine halt with output true; the choice-verifier theorem supplies a polynomial-time language recognizing this event when the choice-string length has the specified polynomial form. Use that language to define a verifier which tests whether the concatenation of the input and random bits belongs to it. Its efficiency follows from closure of polynomial time under this concatenation construction.

Fix an input $x$. Write $B=c(|x|^e+1)$ for the expected-time bound and $Q=(200c)(|x|+1)^e$ for the verifier's random-bit budget. The choice-budget inequality gives $100B\le Q$. The choice verifier's defining property identifies acceptance on a random string of length $Q$ with the event that the nondeterministic machine halts with output true on that string. For a member, the hypothesis gives some number of random bits at which this event has probability at least $2/3-\varepsilon$, for every positive $\varepsilon$. The expected-time tail bound shows that this probability is at most the probability at the truncated budget $100B$ plus $1/100$, and monotonicity in the number of random bits bounds the truncated-budget probability by the one at $Q$. Taking $\varepsilon=2/3-1/100-5/8>0$ therefore forces the probability at $Q$ to be at least $5/8$. A constant-error amplification theorem, applied with base success threshold $5/8$ and two repetitions, upgrades this to the RP threshold $2/3$ while preserving perfect rejection.

For a nonmember, every halting run outputs false. Thus the verifier cannot accept: if it did, the choice-verifier characterization would yield a halting run with output true, contradicting the one-sided output condition. Hence rejection is certain on every random tape.

**Key facts.** `Complexity.exists_choiceVerifier_mem_P`, `Randomized.eff_append_mem`, `Turing.choiceBudget_le`, `Randomized.indicator_eq_true_iff`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.FinNDTM.haltProb_le_truncate`, `Turing.FinNDTM.haltProb_mono`, `Randomized.InRPWith.inRP_of_const`.
