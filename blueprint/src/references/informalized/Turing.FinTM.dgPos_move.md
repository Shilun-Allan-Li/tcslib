<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgPos_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head movement commutes with position transfer

**Claim.** Transferring an input-head position to the longer word and then moving it gives the same position as moving first in the retracted word and then transferring it.

**Proof.** Compare the two positions by their natural-number values. Position transfer preserves the value, and the retracted word and original word have equal lengths. The movement operation therefore computes the same tentative moved value and applies the same boundary rule on either side. The resulting values agree, so the two positions in the finite interval are equal.
