<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.zerosAfterZero_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output on an All-Ones String

**Claim.** For every natural number $j$, the transducer that emits a zero on each bit after it has read a zero produces the empty string on a string of $j$ ones.

**Proof.** Proceed by induction on $j$. For $j=0$, the input is empty, so the transducer produces the empty string. For the successor case, a string of $j+1$ ones begins with a one followed by $j$ ones. In the initial state, reading a one emits nothing and leaves the machine in that state, since it has not yet read a zero. Thus the output is exactly the output on the remaining $j$ ones, which is empty by the induction hypothesis.
