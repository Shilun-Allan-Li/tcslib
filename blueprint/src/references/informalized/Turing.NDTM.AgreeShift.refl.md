<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.AgreeShift.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of Shifted Agreement

**Claim.** A configuration agrees with itself with shift zero and radius $r$: its state, input-head position, and output coincide with themselves, every work-tape head has shift zero, and the tape contents agree on the required cells.

**Proof.** The state, input-head position, and output equal themselves. Each work-tape head position is its own position plus zero. For any tape and cell in the indicated range, the shifted cell is the original cell because the shift is zero, so the two tape contents are equal.
