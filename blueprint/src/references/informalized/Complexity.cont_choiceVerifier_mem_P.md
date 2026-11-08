<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_choiceVerifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Choice-Word Verification

**Claim.** For every binary nondeterministic machine and natural numbers $C,c$, the language of words $y=xu$ where $u$ has length $C(|x|+1)^c$ and makes the machine halt with output $[1]$ on $x$ belongs to $\mathrm P$.

**Proof.** Use the polynomial-time splitting procedure to construct a deterministic machine $M$ that, on input $y$, computes the proposed split and encodes its two parts in time at most $A(|y|+1)^{c+2}$ for some constant $A$ (`computesFunInTime_splitSolve`). Follow $M$ by a buffered simulation of a deterministic machine that checks the split and simulates the nondeterministic machine using the proposed choice word. The split machine’s output is precisely the encoded pair of candidate input and choice word. By the split-answer result, the second machine decides whether this candidate satisfies the required length, halting, and output conditions in at most $3(2|y|+3)$ steps (`cont_split_answer`). The buffered composition starts this second phase in a configuration representing its initial configuration on the computed pair, after some $a\le A(|y|+1)^{c+2}+|y|+2$ steps (`bufferedComp_start`); its subsequent run agrees with the second machine’s run for the stated number of steps (`bufferedSecondCfg_run`). Thus the composite halts with the language indicator as output (`computesInTime_iff`). Finally, since $|y|+1\le (|y|+1)^{c+2}$ and the linear overhead is bounded by a constant multiple of this same power, the total time is at most $(A+13)(|y|+1)^{c+2}$. The polynomial-time characterization then gives membership in $\mathrm P$ (`mem_P_iff`), with any larger bound still valid by monotonicity of running time (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Complexity.cont_split_answer`, `Turing.FinTM.computesInTime_iff`, `Complexity.cont_split_length`, `Complexity.mem_P_iff`, `Turing.FinTM.ComputesInTime.mono`.
