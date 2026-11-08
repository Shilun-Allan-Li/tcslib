<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clOutput_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output from a returned buffer

**Claim.** Under the stated hypotheses, the machine extended with the output procedure computes $w$ on input $x$ within $a+2|w|+4$ steps.

**Proof.** By the first-return lemma (`Complexity.clFirst`), there is a first time $t$ with $0<t\le a$ at which the original machine reaches the returned configuration $d$. Before time $t$ it never enters state $r$. This lets us simulate those first $t$ steps in the extended machine: outside the return state, its transitions agree with the original machine after embedding the original states into the extended state space (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`). At time $t$, the simulated configuration is therefore $d$ with its state embedded. The next step dispatches to the replay procedure. Because $d$ has empty output, has $w$ on the selected tape, and has that tape head at position $|w|$, this step sets up the replay configuration with the head at the end of the buffer. The replay procedure first moves left to the buffer's beginning, then moves right, outputting each bit, and halts after $2|w|+3$ replay steps (`Complexity.clReplay_run`). Thus the extended machine halts with output $w$ after $t+1+(2|w|+3)$ steps. Since $t\le a$, this is at most $a+2|w|+4$; monotonicity of computation time gives the claimed bound.

**Key facts.** `Complexity.clFirst`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Complexity.clReplay_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
