<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepTape_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty and Blank Right Stacks

**Claim.** For every integer frontier and left stack, the tape represented with an empty right stack equals the tape represented with a singleton right stack containing a blank symbol.

**Proof.** Evaluate the two tape functions at an arbitrary coordinate. If it lies to the left of the frontier, both functions use the same left stack. Otherwise, the empty right stack returns blank at every index; the singleton list $[none]$ also returns blank at index zero and, beyond that, has no entry and so returns blank. Hence the functions agree at every coordinate.
