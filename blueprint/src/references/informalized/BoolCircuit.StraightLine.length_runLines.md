<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.length_runLines -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Evaluated Lines

**Claim.** Evaluating a finite list of straight-line statements in order produces a list whose length equals the number of statements.

**Proof.** Induct on the statement list by appending its final statement. The empty list evaluates to the empty list. By the induction hypothesis, the earlier statements produce a list of length equal to their number. Appending one statement appends exactly one evaluated Boolean to that result (`runLines_snoc`), so the output length increases by one and equals the length of the extended statement list.

**Key facts.** `BoolCircuit.StraightLine.runLines_snoc`.
