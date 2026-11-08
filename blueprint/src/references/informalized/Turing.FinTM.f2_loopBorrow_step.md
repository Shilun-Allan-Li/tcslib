<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBorrow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Borrow Step

**Claim.** Starting in the initial search state with the head at $|v|$ and tape contents $vs$, one step produces the stated result: it returns false on an empty suffix, returns true and clears a leading true, or continues the search and changes a leading false to true.

**Proof.** The input-head movement in each transition is zero, so the input position remains $p$ (the zero-movement property of `moveInputPos_zero`). The tape symbol under the work-tape head is the first symbol of $s$, if present, because reading the buffer at position $|v|$ gives $s.head?$ (`f2_loopBuffer_read`). If $s$ is empty, the machine chooses the empty-suffix transition: it enters the result state carrying false, leaves the tape unchanged, and moves the work-tape head one cell left. If $s$ begins with true, it writes false at that cell, enters the result state carrying true, and moves left; the update is exactly the buffer for $v$ followed by false and the remaining suffix (`f2_loopBuffer_write`). If $s$ begins with false, it writes true there, remains in the search state, and moves right; the same buffer-update fact identifies the resulting tape. In each case the output is unchanged, and these componentwise equalities give the asserted configuration.

**Key facts.** `Turing.FinTM.f2_loopBuffer_read`, `Turing.FinTM.f2_loopBuffer_write`, `Turing.moveInputPos_zero`.
