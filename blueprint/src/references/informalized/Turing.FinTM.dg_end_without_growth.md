<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_end_without_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward sweep without growth

**Claim.** When no marked tape head moves left, the augmented simulator takes one stationary step from the backward-writing phase to the left-growth phase, preserving the frontier and both stacks and keeping its head at $z$.

**Proof.** At frontier $z$, the right-stack boundary marker is the symbol read by the simulator; this is exactly the value given by the frontier-read identity (`sweepTape_read`). The condition that no marked head moves left makes the growth test false, so the simulator selects the branch that enters the left-growth phase with the action's optional successor state and makes no stack change. Its transition is stationary, as expressed by `sweepRevCfg_stay`. Both endpoint head positions are $z$, so the one-step span lemma (`dgSpan_one`) establishes the exact transition and the bound $[z,z]$.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepRevCfg_stay`, `Turing.FinTM.dgSpan_one`.
