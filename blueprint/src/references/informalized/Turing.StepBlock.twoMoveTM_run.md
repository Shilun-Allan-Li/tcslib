<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.twoMoveTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running the two-move machine

**Claim.** For every $u\le 2$, the machine started in state $0$ reaches state $u$, moves work-tape head $i$ by $u\delta$, and leaves the other configuration components unchanged.

**Proof.** Proceed by induction on $u$, retaining the bound $u\le2$. At $u=0$, the run is the initial configuration; the state hypothesis identifies its state as $0$, and the head displacement is zero, so the stated configuration agrees with the initial one. For the successor step, the run after $u+1$ steps is one step from the run after $u$ steps (`runFrom_succ_eq_step'`). By induction, that intermediate configuration has state $u$ and head position on tape $i$ equal to its original position plus $u\delta$. Since $u+1\le2$, we have $u<2$, so the transition in state $u$ is the tape action that makes no write, moves head $i$ by $\delta$, leaves other work heads fixed, and advances to state $u+1$. The one-step behavior of this action is given by `step_of_tapeAction_move`. Thus the new head position is the original position plus $u\delta+\delta=(u+1)\delta$, and the state is $u+1$; the input position, tape contents, output, and other head positions remain as claimed.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.step_of_tapeAction_move`.
