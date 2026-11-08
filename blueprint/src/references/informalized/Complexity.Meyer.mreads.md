<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.mreads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Original Work-Tape Readings

**Claim.** In the combined collection of the original work tapes and three additional tapes, the symbols read on the first $k$ tapes are exactly the symbols read by the original work tapes.

**Proof.** Fix any original tape index $i$. The combined reading function is defined by adjoining the readings on the original tapes and the three extra tapes. The index `Fin.castAdd 3 i` lies in the original-tape portion of that combined collection, so evaluation there returns the reading on tape $i$ of the original configuration. Since this holds at every index, the two functions of $i$ agree.
