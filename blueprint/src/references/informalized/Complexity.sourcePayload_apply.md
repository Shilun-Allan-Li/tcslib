<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.sourcePayload_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload shift under one action

**Claim.** For each virtual tape coordinate, the payload at offset $z$ after applying an action is the original payload after its prescribed write and then the coordinate’s head shift, with the input shift clipped at the input boundaries.

**Proof.** Split the virtual coordinate into a work-tape coordinate $j$ or the input coordinate. For a work tape, the updated head is at the old head position plus the action’s movement. Thus the tape position sampled at offset $z$ is the old tape position plus $z$ and that movement; associativity of integer addition puts it in the form used on the right. If the shifted offset is zero, the sampled cell is the head cell: the action’s optional write supplies its new symbol, with the old head symbol used when no write is prescribed. If the shifted offset is nonzero, the sampled cell differs from the old head position, so the update changes nothing there; the original tape value is therefore read. For the input coordinate, the input head’s new position is obtained by the clipped move. The fact that clipping changes the head position by exactly the clipped direction is `clippedMove_correct`; substituting this identity makes the new input offset equal to the old input offset plus the clipped shift. The input payloads then agree, including their boundary tags.

**Key facts.** `Complexity.clippedMove_correct`.
