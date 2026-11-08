<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission of the encoded input split

**Claim.** When $|s|\le |w|$, the controller emits the pair encoding of the prefix of $w$ of length $|s|$ and the remaining suffix, halting after exactly $|s|+|w|+3$ steps without visiting the anchor.

**Proof.** The auxiliary emission machine, started with the input head and candidate positioned as specified, halts after the stated number of steps and outputs the pair encoding of the indicated prefix and suffix (`splitEmit_run`). Simulate this entire run in the controller's emission phase. Every auxiliary state is permitted in this phase, and its transitions agree with the controller's embedded transitions, so the phase simulation lemma gives the corresponding controller run and preserves the anchor-avoidance property (`emitterP2_phase`). The initial emission configuration is the auxiliary start configuration (`emitterP2_emit_initial`). The one-tape frame identification and the candidate-slot update identify the embedded configurations with the controller's tape layout (`emitterP2_one_frame`, `emitterP2_update_candidate`). Taking the state and output of the resulting configuration gives the asserted halting state and output.

**Key facts.** `Turing.FinTM.splitEmit_run`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_emit_initial`, `Turing.FinTM.emitterP2_one_frame`, `Turing.FinTM.emitterP2_update_candidate`.
