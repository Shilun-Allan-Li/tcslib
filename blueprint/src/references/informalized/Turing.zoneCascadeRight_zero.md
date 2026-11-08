<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascadeRight_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Rightward Cascade

**Claim.** If the innermost right zone is nonempty and the innermost left zone has room for one additional cell, then the zero-step rightward cascade has left-side contents equal to the home cell followed by the original left-side contents, and right-side contents equal to the tail of the original right-side contents.

**Proof.** At zero steps, both ranges used in the cascade are empty. Their folds therefore leave the configuration unchanged, so the cascade reduces to a single rightward move. The hypotheses ensure that the move is defined: the left zone has the required room, and the right zone supplies a cell. The rightward-move concatenation property (`zoneSide_moveRight`) then gives the two asserted equalities.

**Key facts.** `Turing.zoneSide_moveRight`.
