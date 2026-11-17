<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_fuel_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Copying Phase

**Claim.** Starting in controller phase $2$ with counter tape storing $v$, payload tape blank on the first $|v|$ cells and otherwise equal to the buffer tape of $vr$, both heads at $|v|$, and output $o$, the host reaches phase $3$ after $|r|+1$ steps. The counter then stores $vr$, the payload tape is blank, and both heads are at $|vr|-1$; the remaining frame data and output are unchanged.

**Proof.** Proceed by induction on the list $r$, generalizing the already-copied prefix $v$. If $r$ is empty, the payload head is at the first blank cell, so the phase-$2$ transition detects the end of the payload, moves both relevant heads one cell left, and enters phase $3$. The payload tape is now blank by the final-tape property of the copy tape (`loopCopy_final`).

For the inductive step, write $r=b::r'$. The payload head scans $b$ at position $|v|$. The phase-$2$ transition writes $b$ at the counter head, advances both heads, and remains in phase $2$. The tape update agrees with appending $b$ to the counter (`bufferTape_append`), while erasing the scanned payload cell gives exactly the representation of the remaining suffix with enlarged prefix (`loopCopy_erase`). Thus one step produces the same setup with prefix $v++[b]$ and suffix $r'$. Apply the induction hypothesis to that setup; the run-length recursion then gives the claimed total of $|r|+1$ steps. At each transition the frame update is governed by `loopControl_apply`, which also makes clear that the output and other frame data are preserved.

**Key facts.** `Turing.FinTM.loopFrame_payload`, `Turing.FinTM.loopCopy_read`, `Turing.FinTM.loopControl_apply`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.loopCopy_erase`, `Turing.FinTM.loopCopy_final`.
