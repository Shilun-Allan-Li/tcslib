<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_borrow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Step

**Claim.** In control phase 8, the host examines the counter bit at the head position. An empty suffix moves to phase 10 and steps the head left; a true bit is changed to false and moves to phase 9 with a left step; a false bit is changed to true and remains in phase 8 with a right step. The input position and output are preserved.

**Proof.** The counter tape stores the concatenated word `pre ++ rest`, and its head is at the length of `pre`. The frame-counter identity (`f2_loopFrame_counter`) identifies the bit read by the transition with the counter contents at this head position; the buffer-read identity (`f2_loopBuffer_read`) says this is exactly `rest.head?`. If `rest` is empty, the transition therefore sees a blank cell, selects phase 10, makes no tape write, and moves the counter head left. If `rest = b :: us`, the transition sees `b`. When `b` is true it writes false at the current cell, selects phase 9, and moves left; when `b` is false it writes true, stays in phase 8, and moves right. The control-action application rule (`f2_loopControl_apply`) translates each selected action into the corresponding updated frame, and the buffer-write identity (`f2_loopBuffer_write`) identifies the changed counter tape with the stated concatenated word. In all three branches the action leaves the input head and output unchanged; the displayed head positions follow from the chosen unit movement.

**Key facts.** `Turing.FinTM.f2_loopFrame_counter`, `Turing.FinTM.f2_loopBuffer_read`, `Turing.FinTM.f2_loopControl_apply`, `Turing.FinTM.f2_loopBuffer_write`.
