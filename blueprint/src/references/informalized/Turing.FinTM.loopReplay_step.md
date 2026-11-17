<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopReplay_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of Payload Replay

**Claim.** A live replay configuration holding PR with head at |P| halts without changing its tape or output when R is empty; when R begins with b, it leaves the tape unchanged, advances the head by one, appends b to the output, and remains live.

**Proof.** The replay machine reads the symbol at the head of its buffer tape. The buffer-reading fact says that when the tape stores P followed by R and the head is at |P|, the symbol read is the head of R (`loopBuffer_read`). If R is empty, this read supplies no bit, so the transition halts, makes no tape or output change, and does not move the head. If R is b followed by a further suffix, the read symbol is b, so the transition emits b and remains live; its tape action makes no write and its head movement is zero, leaving the stored word and head position unchanged by the action. In both cases the input head also stays fixed, by the zero-movement property (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.loopBuffer_read`, `Turing.moveInputPos_zero`.
