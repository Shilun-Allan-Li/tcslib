<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: Clause.eval_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Clause with a First Literal

**Claim.** Placing a literal $l$ before a clause $c$ gives a clause whose evaluation at $x$ is the disjunction of the value of $l$ and the evaluation of $c$ at $x$.

**Proof.** Clause evaluation asks whether any literal in the list evaluates to true. For the list beginning with $l$, this holds precisely when $l$ evaluates to true or some literal in the remaining list $c$ evaluates to true. This is exactly the stated Boolean disjunction.
