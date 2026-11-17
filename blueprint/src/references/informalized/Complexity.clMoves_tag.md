<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMoves_tag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Valid Position Tags

**Claim.** If a Boolean tag correctly marks the input-head boundary positions, the displacement vector computed with that tag equals the vector computed with the tag that is true exactly when the input-head position is nonzero.

**Proof.** Fix a coordinate and compare the two recorded displacements as integers. By the position-change formula (`Complexity.clMoves_correct`), each displacement is the difference between the reference position after the step and the reference position before it. The step and reference positions do not depend on the tag, so these differences are equal. The tag defined by whether the position is nonzero is valid (`Complexity.clTag_valid`), allowing the formula to be applied to it as well as to the given tag. Equality of the integer casts implies equality of the two signs, by injectivity of the cast (`Complexity.clMove_inj`). Since this holds coordinatewise, the displacement vectors agree.

**Key facts.** `Complexity.clMove_inj`, `Complexity.clMoves_correct`, `Complexity.clTag_valid`.
