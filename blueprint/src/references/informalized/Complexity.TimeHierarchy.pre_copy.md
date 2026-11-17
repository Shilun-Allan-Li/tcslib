<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.pre_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the Remaining Input

**Claim.** If the machine is in the copy state with its input head just before the suffix $rest$, then after $|rest|+1$ steps it has halted and appended $rest$ to its original output.

**Proof.** Proceed by induction on $rest$. If $rest$ is empty, the head reads the end marker; the copy-state transition halts without emitting a bit, so one step gives the stated result. If $rest=b::r$, the head reads $b$. The transition emits $b$, moves right, and remains in the copy state. The new configuration is positioned at the start of $r$, with the input suffix now $r$. Apply the induction hypothesis to that configuration: in $|r|+1$ further steps the machine halts and appends $r$. The run-length identity for taking one step first ( `runFrom_succ_eq_step` ) combines these steps; since $|b::r|+1=|r|+2$, the total time is the claimed amount, and the output is the original output followed by $b::r$. The input-symbol identification at a head position (`inputSymbol_at`) and the fact that a positive move advances a head not at the right boundary (`moveInputPos_pos_of_ne_right`) justify the read and updated position in the inductive case. The one-step behavior is supplied by the preprocessing transition equation (`preTM_step`).

**Key facts.** `Complexity.TimeHierarchy.preTM_step`, `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
