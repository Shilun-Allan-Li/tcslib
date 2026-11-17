<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_erase_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the width word

**Claim.** The controller erases the left-bank word while preserving the candidate, right-bank word, and verdict, reaching erasure state $2$ within the stated bound without visiting the anchor.

**Proof.** The auxiliary erasure machine scans the left-bank word and clears its symbols, reaching state $2$ within $2(|u|+1)$ steps while avoiding that terminal state earlier (`emitterP2_erase_first`). Embed this one-tape run into the controller's left-bank slot. Before the auxiliary terminal state, the controller's transition agrees with the embedded erasure transition and the embedded states are not the anchor; the phase simulation lemma therefore transfers both the endpoint and the safety assertion (`emitterP2_phase`). The frame identification and the left-slot update show that this embedding has exactly the controller's desired tape contents: the left bank is empty while the candidate and right bank are unchanged (`emitterP2_one_frame`, `emitterP2_update_left`).

**Key facts.** `Turing.FinTM.emitterP2_erase_first`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_one_frame`, `Turing.FinTM.emitterP2_update_left`.
