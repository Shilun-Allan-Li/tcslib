<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finalizer Endpoint Configuration

**Claim.** Embedding the finalizer’s state-$5$ configuration with the mode-dependent argument word, blank capture tape, origin heads, and mode-dependent output yields the canonical call-machine exit configuration.

**Proof.** Compare the embedded finalizer configuration tape by tape. The layout-case lemma says every call-machine tape is either one of the finalizer’s two selected tapes or belongs to one of the three-tape banks (`emCall_layout_cases`). On the selected pair, the embedding preserves tape contents and head positions (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`), and the pair-layout formula identifies those slots as the argument tape and capture tape (`emCall_layout_pair`). Thus they contain the requested mode-dependent word and blanks, with both heads at the origin. For each bank slot, the pair-selector distinguishes it from the embedded finalizer tapes (`emCall_pair_triple`), so the embedding-frame result shows its tape and head remain the specified blank tape and origin head (`embedEmitTM_frame`). Applying the triple-layout formula identifies these as all blank bank tapes with origin heads (`emCall_layout_triple`). The state, input-head position, and output match directly: the state is exit state $5$, the input-head position is $1$, and the output is the stated mode-dependent word.

**Key facts.** `Turing.FinTM.emCall_layout_cases`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.FinTM.emCall_layout_pair`, `Turing.FinTM.emCall_pair_triple`, `Turing.embedEmitTM_frame`, `Turing.FinTM.emCall_layout_triple`.
