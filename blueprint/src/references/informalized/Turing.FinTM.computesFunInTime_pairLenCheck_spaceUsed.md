<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairLenCheck_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-length check with space control

**Claim.** For natural numbers $C,e$, a finite Boolean Turing machine outputs the bit indicating whether a successful aligned parse $(a,b)$ satisfies $|b|\le C(|a|+1)^e$, returning false on parse failure. Its time is bounded by a constant times $(|x|+1)^{e+1}$, and its space at every time is bounded by a constant times $(|x|+1)^e+|x|+1$.

**Proof.** Take a unary-output machine that, on input $y$, produces a word of length $C(|y|+1)^e$ in time at most $a((|y|+1)^e+|y|+1)$ for some constant $a$ (`f2_unary_sharp`). Feed it the extracted first component by composing it with the machine that extracts that component. The extracted length is at most $|x|$ (`f2_first_length`), so the unary computation's time is bounded by a constant multiple of $(|x|+1)^e+|x|+1$. The composition has this time bound up to the fixed overhead for buffering (`bufferedCompTM_computesInTime`), and increasing the bound preserves its result (`ComputesInTime.mono`). Now apply the pair-count machine to compare the second component's length with the generated unary word's length; this gives the required bit and returns false on parse failure (`f2_pairCount_computes`). Its additional time is linear in the input length, so the total time remains bounded by a constant times $(|x|+1)^{e+1}$. For space, apply the general estimate that a computation of time $T$ on a machine with $k$ work tapes uses at most $k(T+1)$ cells (`f2_space_of_time`). Substituting the established time bound and absorbing the additive one into the same expression yields the asserted space bound, after choosing a sufficiently large constant.

**Key facts.** `Turing.FinTM.f2_unary_sharp`, `Turing.FinTM.f2_first_length`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_pairCount_computes`, `Turing.FinTM.f2_space_of_time`.
