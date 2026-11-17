<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_unary_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Rewind Cost

**Claim.** Starting in the unary-rewind phase at head position $j$, after $j+1$ steps the unary head is at $1$ and the phase is start-center when $last$ is true, and otherwise the first rightward layout phase; all other configuration data are unchanged.

**Proof.** Establish the one-step behavior at head position $j$. The unary tape has its origin exactly at position $0$ (`unaryTape_origin`). At $j=0$, the rewind transition sees that origin, enters the phase determined by $last$, and moves the unary head right to $1$. At $j>0$, it sees no origin, stays in the same rewind phase, and moves the head left from $j$ to $j-1$. In either case the other heads and tapes remain fixed. Induction on $j$ iterates this behavior: the base run consists of the terminal transition followed by zero further steps, and the successor case first rewinds once and then uses the induction hypothesis for the remaining run. The run-length identities are given by the zero-step and successor-step laws (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`); each transition’s effect on the setup configuration follows from `setupCfg_apply`.

**Key facts.** `Complexity.setupCfg_apply`, `Complexity.unaryTape_origin`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
