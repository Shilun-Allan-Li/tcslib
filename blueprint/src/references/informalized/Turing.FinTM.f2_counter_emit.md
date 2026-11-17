<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Halting Output

**Claim.** For every Boolean list $x$, valid input-head position $p$, and Boolean list $bs$, after $|bs|+1$ steps from state $3$, with tape containing $bs$, work-tape head at $0$, and empty output, the counter machine is halted and its output is $bs$.

**Proof.** First observe that at work-tape position $|bs|$ the tape reads no symbol: the list has no entry at that index. By the step-by-step output description (`f2_counter_emit_run`), after $|bs|$ steps the machine is in state $3$, its heads and tape are unchanged, and its output is the prefix of $bs$ of length $|bs|$, hence all of $bs$. One further step takes the machine's state-$3$ transition; at the tape end, that transition halts without changing the output. The run decomposition into the first $|bs|$ steps and one final step is given by `runFrom_succ_eq_step'`. Thus the resulting state is halted and the output remains $bs$.

**Key facts.** `Turing.FinTM.f2_counter_emit_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
