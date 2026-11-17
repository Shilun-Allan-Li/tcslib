<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.complete_negateAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion under negation

**Claim.** Negating every restriction state and complementing the binary vector negates the completed sign vector coordinatewise.

**Proof.** Fix a coordinate and consider its restriction state. If it is free, the complemented bit has sign encoding equal to the negative of the original encoding (`signEncode_binaryCubeComplement`). If it is fixed to $1$, the negated restriction fixes it to $-1$, which is the negative of the original completed value. If it is fixed to $-1$, the negated restriction fixes it to $1$, again the negative of the original value. The equality holds at each coordinate, hence for the vectors.

**Key facts.** `FABL.signEncode_binaryCubeComplement`.
