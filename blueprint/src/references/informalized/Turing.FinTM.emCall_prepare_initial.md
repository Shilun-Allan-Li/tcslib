<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_prepare_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Prepared Configuration

**Claim.** The embedded evaluator configuration formed from the initial right-boundary-wrapper configuration, with its virtual-input tag true and head at position $1$, is the call machine's initial configuration with $\mathrm{arg}$ on its first tape, all other tapes blank, all work heads at the origin, and empty output.

**Proof.** First identify the prepared evaluator configuration itself: on the initial source configuration, the evaluator's call layout is exactly the configuration with initial state corresponding to the right-boundary wrapper's initial state and with $\mathrm{arg}$ stored on the first tape (`Turing.FinTM.emCall_eval_initial`). The call machine's initial tape contents are precisely the same state-word layout, so the states, input positions, and outputs agree. For each work-tape index, the outer embedding is the identity. The selected-tape property of $\mathrm{embedEmitCfg}$ preserves the evaluator's tape contents, and its selected-position property preserves the head positions (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`). Thus the embedded configuration equals the call machine's initial configuration.

**Key facts.** `Turing.FinTM.emCall_eval_initial`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`.
