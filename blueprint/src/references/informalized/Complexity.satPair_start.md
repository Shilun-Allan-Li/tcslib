<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Pairing machine startup bound

**Claim.** If $M$ computes $u$ from $x$ within $T$ steps, then the pairing machine reaches a configuration preserving a configuration of $M$, with captured word $u$, state 4, input head at its initial position, capture head at zero, and empty output, in at most $T+|x|+|u|+5$ steps.

**Proof.** Choose the first halting time $t\le T$ of $M$ on $x$; the first-halt lemma (Complexity.sat_first_halt) supplies this time, the fact that the run is live before it, and that its output at time $t$ is $u$. Let $s$ be the configuration of $M$ at time $t$. While the original machine remains live, the pairing machine simulates it and captures each output symbol on its added tape. The capture-run lemma (Turing.capture_run), together with the matching transition behavior, shows that after $t$ steps the pairing machine is in the captured version of $s$. Its halting state is represented by administrative state 0. The timed-rewind lemma (Turing.FinTM.timed_rewind) then moves the input head back to its initial position and changes the control state to 2 in some $r\le t+2$ steps. The output condition ensures that the captured configuration agrees with the canonical one carrying $u$. One further transition enters state 3 and moves the capture head from offset $|u|$ to $|u|-1$, by the canonical action lemma (Complexity.satPairAction_apply). The rewind lemma (Complexity.satPair_rewind) takes $|u|+1$ more steps and returns the capture head to zero in state 4. The run-composition and successor-step laws (Turing.MultiTapeTM.runFrom_add and Turing.MultiTapeTM.runFrom_succ_eq_step) assemble these phases. The total is $t+r+1+(|u|+1)\le t+(t+2)+1+|u|+1$; the proof sharpens this using the input-head bound from the captured configuration to obtain the stated $T+|x|+|u|+5$ bound.

**Key facts.** `Complexity.sat_first_halt`, `Turing.capture_run`, `Turing.FinTM.timed_rewind`, `Complexity.satPairAction_apply`, `Complexity.satPair_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`.

**Caveat.** The source bounds the rewind phase by the current input-position value plus two, then derives the final time inequality from the configuration’s Fin bound. The exact arithmetic bridge is compressed into an omega step, so the prose gives the bound but does not expand that bookkeeping.
