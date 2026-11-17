<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_erase_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Erasure Run

**Claim.** After $2(|u|+1)$ steps, the eraser has state $2$, a blank tape, and head displacement zero, while preserving input and empty output.

**Proof.** First scan across the word. The scan lemma (`Turing.FinTM.emitterP2_erase_scan`) says that after $|u|$ steps the machine is still in state $0$, the tape still contains $u$, and the head is at displacement $|u|$. At that position the tape is blank, so the next transition enters state $1$ and moves the head back to $|u|-1$; the input head does not move (`Turing.moveInputPos_zero`). Thus after $|u|+1$ steps the configuration is exactly the starting configuration for the backward erasure lemma. That lemma (`Turing.FinTM.emitterP2_erase_back`) erases the word in a further $|u|+1$ steps and reaches state $2$ with head at zero. Decomposing the run at the midpoint (`Turing.MultiTapeTM.runFrom_add`) gives total time $2(|u|+1)$.

**Key facts.** `Turing.FinTM.emitterP2_erase_scan`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.emitterP2_erase_back`.
