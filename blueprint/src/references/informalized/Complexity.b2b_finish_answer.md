<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_finish_answer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Answer Emission

**Claim.** Starting from a configuration whose state is $0$, the host machine's answer phase halts after two steps, appends $b$ to the output, and preserves all work-tape head positions at every time through step two.

**Proof.** In the answer phase, the host machine's transitions agree with those of the answer-emission machine after retagging its states. The run-agreement theorem (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) therefore identifies the host run with the retagged answer-machine run. The answer machine, starting in state $0$, emits the single bit $b$ and halts after two steps (`Complexity.b2b_answer_run`), giving the claimed final state and output. Its first emission step changes only the state and output, not any work-tape head position; its second step halts without moving any head. The one-step run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) makes these intermediate and final configurations explicit, so the head positions agree with the initial ones at times $0$, $1$, and $2$.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Complexity.b2b_answer_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
