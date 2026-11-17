<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleShadowAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle shadow action compatibility

**Claim.** Applying the augmented action to the augmented configuration gives the augmentation of the original successor configuration, with the tag updated according to the marker and the selected tape's movement.

**Proof.** Configurations record a state, input position, work tapes and their head positions, and output. The augmented configuration appends the origin-marker tape and places its head at the selected original tape's head. The augmented action appends a tape action that leaves the marker tape's contents unchanged while moving its head by the selected tape's movement. Thus the original tape coordinates, input position, and output agree on both sides after applying the action, and the appended head position agrees as well. For the state tag, the marker is present precisely at the origin; there the updated tag records whether the selected head's move is not leftward, while away from the origin the tag remains $b$. These coordinate-wise equalities give the claimed configuration equality.
