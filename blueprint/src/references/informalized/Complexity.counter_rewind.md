<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Work-Tape Head

**Claim.** From state $2$ with work head at $j-1$, the machine returns to state $0$ with work head at zero after $j+1$ steps, preserving the tape and input-head position.

**Proof.** Induct on $j$. When $j=0$, the head starts at $-1$; the tape reads empty there, and one transition enters state $0$ with the head at zero. For the successor case, the head starts at the nonnegative position $j$, where $j<|b|$ by the hypothesis. The tape therefore reads the $j$th bit. In state $2$, the transition preserves the tape and moves the work head left while remaining in state $2$. After this first step the configuration is exactly the one required by the induction hypothesis for $j$, so the remaining $j+1$ steps complete the rewind. The run decomposition is $\texttt{runFrom_succ_eq_step}$, and the input head remains fixed under its zero movement ($\texttt{moveInputPos_zero}$); the base case uses the zero-step run identity ($\texttt{runFrom_zero}$).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_zero`.
