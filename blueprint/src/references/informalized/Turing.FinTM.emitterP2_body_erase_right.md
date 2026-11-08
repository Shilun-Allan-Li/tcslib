<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_erase_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the length word

**Claim.** The controller erases the right-bank word while preserving the candidate, left-bank word, and verdict, reaching erasure state $2$ within the stated bound without visiting the anchor.

**Proof.** The auxiliary erasure machine scans the right-bank word and clears its symbols, reaching state $2$ within $2(|v|+1)$ steps while avoiding that terminal state earlier (`emitterP2_erase_first`). Embed this one-tape run into the controller's right-bank slot. On every preterminal auxiliary state the controller transition agrees with the embedded transition, and those embedded states are away from the anchor. The phase simulation lemma transfers the run and its safety property (`emitterP2_phase`). The frame identification and right-slot update then give the controller configuration with the right bank empty and the candidate and left bank unchanged (`emitterP2_one_frame`, `emitterP2_update_right`).

**Key facts.** `Turing.FinTM.emitterP2_erase_first`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_one_frame`, `Turing.FinTM.emitterP2_update_right`.
