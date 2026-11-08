<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.unaryTape_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cell After the Unary Tape

**Claim.** For every $N$, the unary tape with $N$ markers is blank at cell $N+1$.

**Proof.** At $z=N+1$, the position is not the origin, and it is larger than $N$, so it does not lie in the interval of unit-marker cells. Neither defining case for a marker applies, and the tape value is blank.
