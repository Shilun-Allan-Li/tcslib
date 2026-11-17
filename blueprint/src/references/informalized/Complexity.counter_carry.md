<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_carry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the Carry Phase

**Claim.** For a prefix $a$ of $b$, the machine’s carry phase takes $\operatorname{carry}(b)+1$ steps from the stated configuration to state $2$, with the tape holding $a$ followed by the increment of $b$ and the work head at $|a|+\operatorname{carry}(b)-1$.

**Proof.** Proceed by induction on $b$. If $b$ is empty, or begins with $0$, one transition takes the machine directly to state $2$, writes the incremented bit, and moves the work head left; these are exactly the stated results because the carry length is zero. If $b$ begins with $1$, the single-step rule writes $0$ and moves right while remaining in state $1$. Apply the induction hypothesis to the remaining suffix, now with prefix $a$ followed by $0$. Its carry length is one less than the original carry length, so the total number of transitions is the initial transition plus the suffix’s carry-phase transitions, namely $\operatorname{carry}(b)+1$. The suffix is incremented by the induction hypothesis, giving precisely the increment of the original word; the head position likewise simplifies to the claimed value. The transition and run-length identities used here are the one-step carry rule ($\texttt{counter_carry_step}$), the decomposition of a run into its first step and remaining run ($\texttt{runFrom_succ_eq_step}$), and the zero-step run identity ($\texttt{runFrom_zero}$).

**Key facts.** `Complexity.counter_carry_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
