<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMoves_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Displacements Match Position Changes

**Claim.** For a configuration whose Boolean tag correctly marks the two boundary positions, each reference position after one machine step is its previous reference position plus the displacement recorded at that coordinate.

**Proof.** Split according to whether the machine is halted. In the halted case, the machine leaves the configuration unchanged and every recorded displacement is zero, so the equality follows. In an active state, apply the fact that a valid virtual tag makes the virtual input-head movement agree with the actual bounded input-head movement (the first conclusion of `Turing.FinTM.virtualMove_correct`). Then split the coordinate into the input-head coordinate and a work-tape coordinate. For the input head, that fact is exactly the required equality, with sides rearranged. For a work tape, `Action.apply` updates its head position by adding the transition's recorded movement, which is precisely the corresponding component of `clMoves`.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.virtualMove_correct`.
