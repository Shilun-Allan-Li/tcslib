<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_erase_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Erasure

**Claim.** Starting with $u$ under the eraser's head at displacement $|u|-1$ in state $1$, after $|u|+1$ steps the tape is blank and the machine is in state $2$ with its head at zero, preserving input and empty output.

**Proof.** Induct on the word $u$ by building it from the right. If $u$ is empty, one step from state $1$ gives state $2$; the tape is already blank, the head stays at zero, and the input position and output are unchanged. For the induction step, write the word as $u\mathbin{++}[b]$. Its initial head displacement $|u\mathbin{++}[b]|-1$ equals $|u|$. The first step erases the final symbol at that location and moves the head left to $|u|-1$, leaving exactly the buffer for $u$ (`Turing.FinTM.catalogBuffer_erase`). The input head remains fixed, and the output remains empty. The remaining $|u|+1$ steps now satisfy the induction hypothesis, giving the blank tape, state $2$, and head position zero. The run decomposition after one step (`Turing.MultiTapeTM.runFrom_succ_eq_step`) combines these steps into the stated total duration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nil`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.catalogBuffer_erase`.
