<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.writeAdvTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing While Advancing

**Claim.** Starting in state $0$, the writing machine finishes after $|w_0|+1$ steps with $w_0$ written from the initial head position on tape $i$ and the head advanced by $|w_0|$. Every intermediate positive time before completion has a state other than $0$, and all heads remain within the stated bounds.

**Proof.** First, the scan description of the run identifies every time $r\le |w_0|$ with the configuration obtained after writing the first $r$ symbols and advancing tape $i$ by $r$ cells (`scan_adv_run`). At the next step, the transition for the terminal phase makes no work-tape change and enters state $0$; the one-step run equation expresses this final step as applying the transition to the preceding configuration (`runFrom_succ_eq_step'`, `step_of_inputMoveAction`). This gives the asserted final configuration: the written interval contains the symbols of $w_0$ in order, and outside it the original tape contents are retained. For a time strictly between zero and the completion time, the scan is still in one of its writing states, so its state cannot be $0$. During the scan, the selected head has advanced by a number of cells between zero and $|w_0|$, while every other head is stationary; the terminal step advances none of them. These facts give the stated head bounds at every time, including completion.

**Key facts.** `Turing.scan_adv_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.step_of_inputMoveAction`.
