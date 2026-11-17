<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.Shape3.valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Three-Line Program

**Claim.** Each statement in the program associated to a three-line shape uses only input literals or values from earlier lines: the first two use input literals, and the third uses the first and second lines.

**Proof.** A statement index in the three-entry list must be $0$, $1$, or $2$. At indices $0$ and $1$, both operands are literals, and every literal is valid before any line (`BoolCircuit.SLOperand.lit_before`). At index $2$, the operands are lines $0$ and $1$, whose indices are both less than $2$. Hence every statement uses only inputs or earlier lines.

**Key facts.** `BoolCircuit.SLOperand.lit_before`.
