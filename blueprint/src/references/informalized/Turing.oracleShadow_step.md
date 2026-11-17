<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleShadow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle shadow simulation for one step

**Claim.** If the selected tape head lies on the side of the origin indicated by $b$, one step of the original machine admits an updated side tag, and the shadow machine's successor is the augmentation of the original successor with that tag.

**Proof.** Split according to whether the original configuration is halted. In the halted case, both machines remain at their current configurations; retaining $b$ preserves the side condition and the shadow configuration is unchanged. Otherwise let $a$ be the transition action chosen by the original machine. The side-move fact (`oracleSide_move`) says that after the selected head moves by the amount specified in $a$, the updated tag still describes its side: at the origin it records whether the move is non-leftward, and away from the origin it stays unchanged. The shadow machine reads the original work-tape symbols on its first $n$ tapes and reads the origin marker on its appended tape. Its action is therefore precisely the shadow of $a$ with that marker and the current tag. Action compatibility (`oracleShadowAction_apply`) identifies the resulting configuration with the augmentation of the original successor using the updated tag.

**Key facts.** `Turing.oracleSide_move`, `Turing.oracleShadowAction_apply`.
