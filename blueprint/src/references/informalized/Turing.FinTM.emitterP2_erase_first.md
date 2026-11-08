<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_erase_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return of the Eraser

**Claim.** The eraser first reaches state $2$ at some positive time no later than $2(|u|+1)$, and at that time has a blank tape and head position zero, with input and output unchanged.

**Proof.** The complete erasure run (`Turing.FinTM.emitterP2_erase_run`) reaches the specified state-$2$ configuration by time $2(|u|+1)$. Apply the first-entry lemma (`Turing.FinTM.emitter_first_entry`) to stop states consisting of state $2$. Its fixed-point condition holds because the transition in that state is the zero-movement control action, which leaves the whole configuration unchanged (`Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`). The lemma therefore gives a time no later than the full-run bound, with no earlier configuration in state $2$, and with the same endpoint. This time cannot be zero: the starting configuration is in state $0$, whereas the endpoint is in state $2$.

**Key facts.** `Turing.FinTM.emitterP2_erase_run`, `Turing.FinTM.emitter_first_entry`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
