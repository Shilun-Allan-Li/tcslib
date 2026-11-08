<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.restrictCircuit_eval_of_onFirst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Under Dependence on Initial Variables

**Claim.** If $m\le n$ and a circuit's value on every assignment depends only on the first $m$ variables through $f$, then restricting the circuit to those variables, with any padding assignment on the rest, evaluates at $y$ to $f(y)$.

**Proof.** By the evaluation theorem for restriction, the restricted circuit at $y$ equals the original circuit evaluated on the extension that uses $y$ for the first $m$ variables and the padding assignment thereafter (`restrictCircuit_eval`). The assumed dependence says this value is $f$ applied to the first $m$ coordinates of that extension. Those coordinates are exactly $y$, so the result is $f(y)$.

**Key facts.** `BoolCircuit.restrictCircuit_eval`.
