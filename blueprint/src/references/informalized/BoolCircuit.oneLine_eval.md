<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.oneLine_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a single gate

**Claim.** The straight-line program consisting of one gate $o$ applied to signed input literals $l_1,l_2$ evaluates on assignment $x$ to $o$ applied to the truth values of those literals.

**Proof.** The program has length one (`BoolCircuit.oneLine_length`), so its evaluation reads the value of its sole statement. Running that statement on an initially empty list of prior line values evaluates its two operands and applies $o$. Each literal's evaluation is the Boolean comparison between the assigned input value and the literal's sign (`BoolCircuit.SLOperand.lit_eval`). Thus the result is $o$ applied to $(x(l_1.1)=l_1.2)$ and $(x(l_2.1)=l_2.2)$, as claimed.

**Key facts.** `BoolCircuit.oneLine_length`, `BoolCircuit.SLOperand.lit_eval`.
