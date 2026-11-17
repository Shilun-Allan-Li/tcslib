<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockTape_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cell Beyond the Word

**Claim.** For every Boolean word $w$, the captured clock tape is blank at coordinate $|w|+1$.

**Proof.** At $z=|w|+1$, the coordinate is nonzero, so the clock tape uses the buffered word rather than placing the origin marker. Its buffer index is $z-1=|w|$, which is exactly one past the last index of $w$. Thus the list lookup is absent, and encoding that absent symbol still gives blank.
