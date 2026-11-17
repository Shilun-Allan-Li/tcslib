<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Halts with the Stored Word

**Claim.** Starting in the emit state with tape word $b$, after $|b|+1$ steps the machine is halted and its output is $b$.

**Proof.** First run the emit phase for $|b|$ steps. The prefix-emission result says the machine remains in the emit state, its work head reaches position $|b|$, its tape is unchanged, and its output is the prefix of $b$ of length $|b|$, hence all of $b$ ($\texttt{counter_emit_run}$). At that position the tape reads empty, since it is just past the end of the finite word. One more transition therefore takes the machine to its halted state without adding a symbol to the output. The run decomposition into a run of length $|b|$ followed by one step is given by $\texttt{runFrom_succ_eq_step'}$.

**Key facts.** `Complexity.counter_emit_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
