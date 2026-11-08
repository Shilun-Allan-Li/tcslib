<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldMove_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative translated positions

**Claim.** For a nonnegative position, translating any move direction using its zero flag gives a displacement whose addition to the position remains nonnegative.

**Proof.** Split according to whether the position is zero, the side flag, and the move direction. At position zero, the zero flag is true, so a move that would cross below zero is translated to zero displacement; the other translated displacements are zero or positive. At a positive position, the zero flag is false, and the translated displacement is either zero or one unit toward or away from the origin. Thus adding it to the position cannot produce a negative value.
