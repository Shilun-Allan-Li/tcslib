<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_fill -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step of an Outward Allocation Pass

**Claim.** Under the unit-marker and origin-mark assumptions, one outward allocation step advances the allocation index cyclically, moves the unary head forward exactly when the index is $2$, advances the guide head in the chosen direction, and extends the filled guide by one cell.

**Proof.** The origin-mark hypothesis for the original guide persists in the partially filled guide: `guideFill_origin` shows that the filled guide still has its origin mark exactly at coordinate zero. Together with the unit marker at the unary head, this meets the conditions of `setupCfg_layout_step`. That one-step result advances the phase index to its cyclic successor, advances the unary head precisely at index $2$, moves the guide head one cell in the selected direction, and writes the appropriate guide mark at the old head position. The identity `guideFill_next` identifies this updated tape with the guide filled through $j+1$ cells; the remaining equalities are the integer head-position arithmetic.

**Key facts.** `Complexity.guideFill_origin`, `Complexity.setupCfg_layout_step`, `Complexity.guideFill_next`.
