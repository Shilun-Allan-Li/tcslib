<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.tmove_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Preserved by a Tape Move

**Claim.** For a valid segment index and valid tape position, any move direction leaves the segment index within the sequence and produces a position valid for the resulting segment.

**Proof.** Split into the three move directions and the three position forms: left boundary, cell, and right boundary. A zero move leaves both unchanged. For a cell, a positive move either changes only its phase flag, advances to the next cell when that cell lies within the word, or reaches the right boundary; a negative move either changes only the phase flag, reaches the left boundary at cell zero, or decreases the cell index. In each cell case the assumed validity and the branch condition ensure that any resulting cell index remains below the word length. At a right boundary, a positive move either advances to the next segment when one exists or stays at the final right boundary; a negative move goes to the left boundary for an empty word or to its final cell. At a left boundary, a positive move goes to the right boundary for an empty word or to cell zero; a negative move goes to the previous segment's right boundary when one exists or stays at the first left boundary. The conditions on the segment index ensure that every segment change stays in range, and boundaries are valid by definition.
