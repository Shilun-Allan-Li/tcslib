<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.Shape3.prog_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Three-Line Program

**Claim.** The program associated to a three-line shape evaluates to the third operation applied to the first two operations, with each literal evaluated as equality between its input value and its sign.

**Proof.** The associated program has length three (`BoolCircuit.Shape3.prog_length`), so its output is the value of its third line. Expanding the three statements shows that the first two apply $o_1$ and $o_2$ to their respective pairs of literals, while the third applies $o_3$ to the values of those two lines. Each literal evaluates to the equality of its input coordinate with its Boolean sign (`BoolCircuit.SLOperand.lit_eval`). Substituting these four literal values into the three line operations gives the stated expression.

**Key facts.** `BoolCircuit.Shape3.prog_length`, `BoolCircuit.SLOperand.lit_eval`.
