<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean :: Complexity.LogProg.compile_correct_from -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Simulation from an Arbitrary Configuration

**Claim.** If the register-program run from an arbitrary configuration obeys the head bounds and its calls satisfy the stipulated conditions, then the compiled machine reaches the corresponding compiled configuration at time $N$, with all register and decider-head bounds maintained throughout.

**Proof.** Use induction on $N$. At $N=0$, take time zero: the compiled machine already starts at the seam of $c_0$, and the assumed register bounds give the register part of the invariant; the adjoined decider heads start at zero.

For the successor case, the induction hypothesis simulates the first $N$ register-program steps and preserves the bounds up to the corresponding compiled time $T$. Let $c$ be the register-program configuration at time $N$. Establish a simulation of its next step, distinguishing its state and whether that state is a call state. If the state is halting, no compiled step is needed; the register bounds at time $N$ and the blank decider tapes give the invariant. If it is an ordinary program state, one compiled step simulates one program step by the seam-step identity (`step_seam_prog`). The invariant at the start comes from the bound at time $N$, and at the endpoint from the assumed bound at time $N+1$.

If it is a call state, the call hypotheses provide distinct arguments, the correct input position and register representations, and a clean decider run with head bound $B$. The call simulation theorem (`call_run`) therefore simulates that call, reaches the seam of the next register-program configuration, and bounds decider heads throughout this segment. For each original register, the call simulation supplies its head bounds if it is an argument register; if it is not an argument register, its head is unchanged and the bound at time $N$ applies. Thus the next-step simulation preserves all bounds.

Finally concatenate the first $N$-step compiled run and this one-step simulation using the run-addition law (`runFrom_add`). The invariant holds over the combined run by the interval concatenation principle (`runFrom_forall_append`), and the endpoint is the seam of the register-program configuration at time $N+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.LogProg.call_run`, `Complexity.LogProg.rrun_succ`, `Complexity.LogProg.step_seam_prog`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.LogProg.runFrom_forall_append`.
