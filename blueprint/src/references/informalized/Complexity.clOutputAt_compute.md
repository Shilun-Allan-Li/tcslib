<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clOutputAt_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning a Buffer with a Head at or Before Its End

**Claim.** Under the stated hypotheses, the machine formed by extending $A$ with the output procedure computes $w$ on input $x$ within $a+j+|w|+4$ steps.

**Proof.** The machine $A$ first reaches the specified configuration $d$ at some first time $t\leq a$ when it enters state $r$. This follows from the first-entry lemma for an idle return state; because the initial state is not $r$, this first time is positive. The original computation can be reproduced by the extended machine up to time $t$: before that time it remains in the original state space and follows $A$’s transitions. At the next step, the extension switches into its replay procedure, with the selected tape containing $w$, its head at position $j$, and the output still empty. The replay procedure moves to the beginning of the buffer and then reads and emits its symbols, ending with output $w$ after $j+|w|+3$ further steps. Combining the initial segment and replay, the extended machine has halted with output $w$ after $t+1+(j+|w|+3)$ steps. Since $t\leq a$, this is at most $a+j+|w|+4$, and the computation-time monotonicity theorem permits the stated time bound.

**Key facts.** `Complexity.clFirst`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.FinTM.controlAction_apply`, `Complexity.clPlaced_run`, `Complexity.clReplay_from`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
