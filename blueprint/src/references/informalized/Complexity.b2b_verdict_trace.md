<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_verdict_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace of the Verdict Machine

**Claim.** For the verdict machine, the first step changes the state from left to read and moves tape $i$ one cell left without changing other configuration data. The second step records the bit $b$ found there, erases that cell, and leaves the head at its new position.

**Proof.** In state left, the machine makes a tape action on tape $i$ that moves left without writing. The one-step transition formula for such an action (`Turing.step_of_tapeAction_move`) therefore gives the asserted state and head update; the input head stays fixed because its movement is zero (`Turing.moveInputPos_zero`). In state read, the hypothesis says the cell now under the head contains $b$. The machine’s transition writes blank there and enters done with value $b$, so the corresponding write-action formula (`Turing.step_of_tapeAction_write`) gives the updated tape and unchanged work-head position. The successor-step identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies this with the two-step run. Since the requested time is at most two, these two computations and the initial configuration exhaust all cases.

**Key facts.** `Turing.step_of_tapeAction_move`, `Turing.moveInputPos_zero`, `Turing.step_of_tapeAction_write`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
