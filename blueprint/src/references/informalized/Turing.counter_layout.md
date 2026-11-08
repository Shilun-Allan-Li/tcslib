<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter-Loop Configuration Layout

**Claim.** The counter-loop configuration has state $q$, the same input-head position and output as $c$, and work tapes and head positions formed by appending $ct$ and $cp$ as the final tape and head position.

**Proof.** Unfold the counter-loop configuration: it embeds the body configuration into the first $k$ tapes, supplies $ct$ and $cp$ on unused tapes, and changes the state to the requested counter-loop state. To identify the final tape and head, the proof uses a one-step-zero run of a machine that leaves its tapes unchanged. The embedding frame theorem then says the unused final tape and head retain their supplied values, while the embedding theorems for selected tapes identify each of the first $k$ tapes and heads with those of $c$ (Turing.embedEmitTM_frame, Turing.embedEmitCfg_selected_tape, Turing.embedEmitCfg_selected_pos). The input position and output are preserved as well; the zero-step run is the identity (Turing.MultiTapeTM.runFrom_zero). Extensionality of configurations now gives exactly the displayed layout.

**Key facts.** `Turing.embedEmitTM_frame`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.MultiTapeTM.runFrom_zero`.
