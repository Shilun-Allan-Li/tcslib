<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol After Masking

**Claim.** After replacing the input by the constant word of copies of $z$, the scanned input symbol is the image of the original scanned symbol under the map that sends every symbol to $z$ and preserves absence.

**Proof.** The input-head position is retained by masking, and the new input has the same length as the old one. Thus the head is at the left boundary, at the right boundary, or at an interior position in exactly the same cases before and after masking. At either boundary both scanned symbols are absent. At an interior position the original input symbol is replaced by $z$, which is exactly its image under the stated map.
