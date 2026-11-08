<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.inBPP_of_mem_BPP_ExpPTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected-Time Machines Yield BPP

**Claim.** If a nondeterministic machine has polynomially bounded expected halting time and can achieve acceptance probability arbitrarily close to $2/3$ on every input, then its language belongs to BPP.

**Proof.** Choose witnesses for the expected-time randomized machine and its polynomial bound, and call the machine $N$. As before, the choice-verifier theorem gives a polynomial-time decidable language encoding accepting computations; use its membership test on the input followed by the random choice string as the verifier. The append-membership construction ensures this verifier is efficient (\texttt{Complexity.exists\_choiceVerifier\_mem\_P}, \texttt{Randomized.eff\_append\_mem}).

Fix an input $x$. Let $B$ be the polynomial bound on the sum of the probabilities of not having halted by each time up to a cutoff, and let $Q$ be the verifier's choice-string length. The choice-budget inequality gives $100B\le Q$ (\texttt{Turing.choiceBudget\_le}). The expected-time truncation bound says that, at any finite cutoff, the probability of halting with a specified output is at most the probability at cutoff $100B$ plus $1/100$ (\texttt{Turing.FinNDTM.haltProb\_le\_truncate}); halting-output probability is nondecreasing as the cutoff grows (\texttt{Turing.FinNDTM.haltProb\_mono}).

These bounds force the probability of halting with the correct one-bit output by time $Q$ to be at least $5/8$. Indeed, if it were smaller, choose the hypothesis's approximation to $2/3$ with error $1/100$; the truncation estimate and monotonicity would then contradict that approximation. The computation-encoding property identifies verifier acceptance with halting and outputting true (\texttt{Randomized.indicator\_eq\_true\_iff}, \texttt{Turing.FinNDTM.haltRun\_eq\_some\_iff}); for a nonmember, the same reasoning applies to output false. Probability monotonicity transfers these output events to the verifier's corresponding answer events (\texttt{Randomized.randProb\_mono}).

Thus the constructed verifier has success probability at least $5/8$ on each input. The polynomial-time model is closed under majority, and the amplification theorem upgrades this fixed advantage to the standard BPP bound (\texttt{Randomized.polyTimeModel\_closedUnderMajority}, \texttt{Randomized.InBPPAt.inBPP\_of\_5\_8}).

**Key facts.** `Complexity.exists_choiceVerifier_mem_P`, `Randomized.eff_append_mem`, `Turing.choiceBudget_le`, `Turing.FinNDTM.haltProb_le_truncate`, `Turing.FinNDTM.haltProb_mono`, `Randomized.indicator_eq_true_iff`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Randomized.randProb_mono`, `Randomized.polyTimeModel_closedUnderMajority`, `Randomized.InBPPAt.inBPP_of_5_8`.
