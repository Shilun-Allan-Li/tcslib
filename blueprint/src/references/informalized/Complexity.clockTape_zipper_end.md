<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockTape_zipper_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End Zipper of a Captured Word

**Claim.** For every bit word $w$, the zipper with frontier at $1+|w|$, left list consisting of the reversed encoded word followed by the origin marker, and empty right list equals the captured clock tape of $w$.

**Proof.** The captured clock tape has the zipper representation with frontier $1$, left list containing the origin marker, and right list the encoded word (`Complexity.clockTape_zipper`). Shifting the zipper frontier across that right list moves the frontier to $1+|w|$, places the reversed encoded word before the origin marker on the left, and leaves an empty right list. This is the zipper shift identity (`Complexity.sweepTape_shift`), so the resulting end zipper represents the same tape.

**Key facts.** `Complexity.clockTape_zipper`, `Complexity.sweepTape_shift`.
