<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.takeTrues_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Leading-One Split

**Claim.** If removing the longest initial run of ones from $x$ yields run length $k$ and remainder $y$, then $k+|y|=|x|$.

**Proof.** Induct on the bit string. The empty string gives the equality immediately. For a nonempty string, if its first bit is $0$, the procedure returns run length zero and leaves the string unchanged, so the equality follows directly. If its first bit is $1$, the procedure recurses on the tail, then increases the run length by one. The induction hypothesis gives the length equality for the tail; adding one to both the run length and the tail length yields the equality for the original string.
