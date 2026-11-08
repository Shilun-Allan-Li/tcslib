<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.preS_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Program Precondition

**Claim.** For every natural number $E$, oracle, input string $x$, and machine configuration $a$, the configuration satisfies the program precondition for the machine determined by $E$ and $x$.

**Proof.** If the configuration has no current label, its precondition holds directly. Otherwise, inspect the current label. For the parameterized increment label, split according to whether its index is below $E$; the program definition then reduces the precondition to a direct check in either branch. For each of the move, doubling, subtraction, halving, copy, and shift loop labels, check the finitely many possible phases against the corresponding instruction definition. All other labels reduce to the precondition clauses for equality tests, encoded-input tests, or oracle calls; the program's fixed register choices satisfy those clauses. Thus every label and phase meets the required precondition.
