<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satScan_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time of the Finite-State Scanner

**Claim.** For a finite state set $S$ with decidable equality, transition function $\delta$, start state $s_0$, and acceptance predicate $A$, the scanner computes $[A(\operatorname{foldl}(\delta,s_0,x))]$ on each Boolean word $x$ in exactly $|x|+1$ steps.

**Proof.** Fix $x$ and use the computation-time characterization, which reduces the claim to proving that the run is halted and has the required output at the stated time. The scanner’s initial configuration is the configuration with state $s_0$, head at the start of $x$, and empty output; equality of these configurations follows from the zero-work-tape extensionality principle (`Cfg.ext_zero_tapes`). Apply the complete-scan lemma `satScan_run` to the entire input, taking the prefix empty and the suffix equal to $x$. It says that after $|x|+1$ steps the scanner is halted and its output is the acceptance bit of the fold of the transition function over $x$. These are exactly the required conditions.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.Cfg.ext_zero_tapes`, `Complexity.satScan_run`.
