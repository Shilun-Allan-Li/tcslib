<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_borrow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Borrow Step

**Claim.** From phase $8$, the host inspects the counter cell at the end of the prefix: it exits to phase $10$ on a blank, enters phase $9$ after changing a true bit to false, and changes a false bit to true while continuing in phase $8$. The other framed data and empty output are preserved.

**Proof.** The counter head is at $|u|$, so the buffer-read identity says that the scanned symbol is the head of the suffix $v$. If $v$ is empty, the scanned cell is blank; the controller moves left without writing and enters phase $10$. If the head of $v$ is true, it writes false at that cell, moves left, and enters phase $9$. If the head is false, it writes true, moves right, and remains in phase $8$. In the latter two cases, the buffer-write identity turns the pointwise tape update into the corresponding changed list. Applying the control-action description gives these successor configurations; all unspecified tracks, the input position, and output retain the frame values.

**Key facts.** `Turing.FinTM.loopFrame_counter`, `Turing.FinTM.loopBuffer_read`, `Turing.FinTM.loopControl_apply`, `Turing.FinTM.loopBuffer_write`.
