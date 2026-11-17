<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_bank_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleaner Return Advances the Blank Prefix

**Claim.** Embedding the cleaner’s blank configuration in state $3$ into the three slots for tape $i$ changes the bank frame with its first $i$ entries blank into the frame with its first $i+1$ entries blank and the cleaner in its return state for tape $i$.

**Proof.** Compare the embedded configuration and the target frame tape by tape. The layout case theorem (`emCall_layout_cases`) divides the slots into the argument and capture slots and the three slots belonging to each source tape. On the argument and capture slots, the embedding leaves the frame values unchanged, as those slots lie outside the cleaner’s three-slot image; the pair-layout identity (`emCall_layout_pair`) identifies their values. For a source tape $j$, the triple-layout identity (`emCall_layout_triple`) identifies its data, span-marker, and origin slots. If $j=i$, the cleaner’s blank tapes and heads at $0$ give exactly the blank data and marker entries required in the next frame; the origin entry is the boundary marker value specified there. If $j\ne i$, the embedding leaves those slots unchanged, and the condition $j<i+1$ is equivalent to $j<i$ for such $j$, so their prior blank-or-run values agree with the next frame. The triple selection facts (`emCall_triple_inverse`, `emCall_triple_other`, and `emCall_triple_pair`) justify which slots belong to the embedded cleaner and which do not; the selected-tape and selected-position facts (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`) transfer the cleaner’s three tape values and head positions to their corresponding slots. The states agree by the specified embedding, and the input position and output are unchanged. Hence the configurations are equal.

**Key facts.** `Turing.FinTM.emCall_layout_cases`, `Turing.FinTM.emCall_layout_pair`, `Turing.FinTM.emCall_layout_triple`, `Turing.FinTM.emCall_triple_inverse`, `Turing.FinTM.emCall_triple_other`, `Turing.FinTM.emCall_triple_pair`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`.
