<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluator Startup Bound

**Claim.** If $M$ computes $u$ on $w$ within time $T$, the evaluator reaches the canonical formula-phase configuration with certificate $u$, head at $0$, and bits true and false, within $T+|w|+|u|+5$ steps.

**Proof.** 1. Choose the first halting time $t\le T$ of $M$ on $w$. The first-halt result supplies a run that stays unhalted before $t$, halts at $t$, and has output $u$ (`Complexity.sat_first_halt`). Let the saved configuration be $M$'s configuration at time $t$. The evaluator's capture simulation follows this run, because the host transition in an embedded machine state is the captured original transition; the simulation is valid through time $t$ by the no-earlier-halting hypothesis (`Turing.capture_run`). At that time its captured configuration has the evaluator's initial control state for the rewind phase, and the captured output is $u$.
2. The evaluator's timed rewind scans left across the input to its left boundary and then moves right into the next control state. The bound on this extra time is at most the current input-position value plus two (`Turing.FinTM.timed_rewind`). The resulting configuration is the canonical one in the intermediate state, with certificate head at $|u|$; identifying it uses the fact that the saved output is $u$.
3. One evaluator transition changes the intermediate state to the next control state and moves the certificate head left to $|u|-1$, leaving the input head fixed (`Complexity.satEvalAction_apply` and `Turing.moveInputPos_zero`). Now apply the certificate rewind result with $n=|u|$, destination the formula phase with bits true and false and skip cleared. It returns the certificate head to $0$ in $|u|+1$ steps (`Complexity.satEval_rewind`).
4. Concatenating these run segments gives time $t+r+(|u|+2)$, where $r$ is the timed rewind duration. The rewind bound and the encoded input-position bound give $t+r+(|u|+2)\le T+|w|+|u|+5$, as required.

**Key facts.** `Complexity.sat_first_halt`, `Turing.capture_run`, `Turing.FinTM.timed_rewind`, `Complexity.satEvalAction_apply`, `Turing.moveInputPos_zero`, `Complexity.satEval_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
