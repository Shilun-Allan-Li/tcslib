<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finalizer Entry Configuration

**Claim.** Embedding the finalizer’s state-$0$ configuration, with the argument and capture words at their specified heads and empty output, gives the cleanup frame at time $T$ with all data, marker, and origin banks blank, their heads at the origin, and control at finalizer entry.

**Proof.** Partition the call-machine tapes using the layout-case lemma: two are the finalizer’s selected pair, while all others are indexed by a work tape and one of its data, marker, or origin slots (`emCall_layout_cases`). On the selected pair, the embedding preserves contents and head positions (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`), and the pair-layout formula identifies the argument and capture slots (`emCall_layout_pair`). On each remaining slot, the pair embedding does not select it (`emCall_pair_triple`), so the embedding-frame result leaves its tape and head at the specified blank and origin values (`embedEmitTM_frame`). The triple-layout formula identifies those values with the cleanup frame’s data, marker, and origin banks (`emCall_layout_triple`). These comparisons establish the tape and head fields; the control state, input-head position, and empty output agree directly by the definitions of the embedded configuration and frame.

**Key facts.** `Turing.FinTM.emCall_layout_cases`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.FinTM.emCall_layout_pair`, `Turing.FinTM.emCall_pair_triple`, `Turing.embedEmitTM_frame`, `Turing.FinTM.emCall_layout_triple`.
