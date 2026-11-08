<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_backward_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Backward Sweep Step

**Claim.** When the guide tape is the fixed guide of radius $R$ and $g\ne -R-1$, a step from the backward phase at guide position $g$ preserves the base configuration, $u$, the source-state and answer registers, and the output; it moves the guide head to $g-1$, replaces the carry registers by the decoded current payloads at $g$, and writes the specified movement-dependent payload at coordinate $g$ on each lane.

**Proof.** Use the general one-step description for the decorated data machine (`dataCfg_step`). The schedule component is in the backward phase, so its backward transition moves the guide head to $g-1$ unless it is at the left edge. The excluded-coordinate hypothesis rules out that edge: by the characterization of the left-edge guide symbol (`guideTape_left`), the guide is not at the left marker. Consequently the schedule transition remains in the backward phase, and the base configuration and the other schedule heads are preserved (`macroCfg_backward`). The guide-head interpretation in the macro configuration identifies the symbol read there with the guide tape at $g$ (`macroCfg_guide`).

The visitor for this phase leaves the source-state and answer registers unchanged, replaces the carry registers by the current payload decoded from each tape cell at $g$, and writes a cell at $g$ whose current payload is the cached left neighbor for a leftward virtual move, the current payload for a stationary move, or the carried payload for a rightward move. Its cached-neighbor field is blank. It emits no output, so the output word remains unchanged. Substituting these visitor and schedule updates into the decorated-machine step formula gives the claimed configuration.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_backward`, `Complexity.guideTape_left`, `Complexity.macroCfg_guide`.
