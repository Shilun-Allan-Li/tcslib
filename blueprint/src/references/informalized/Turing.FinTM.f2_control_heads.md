<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_control_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional control head positions

**Claim.** The work-head vector in the conditional machine's control configuration consists of the detector's head positions, zero positions for both branch machines' tapes, and the length of the detector configuration's output as the final coordinate.

**Proof.** Evaluate the head-position function separately on the first block of tape indices and on the remaining indices. On the first block, the control configuration retains the detector configuration's head positions, by the definition of the left configuration embedding; the added branch tapes are initialized with head position zero. On the final, capture-tape coordinate, the capture configuration places its head at the length of the stored prefix followed by the detector output. Here the stored prefix is empty, so this is exactly the length of the detector output. Together these coordinate descriptions give the stated vector equality.
