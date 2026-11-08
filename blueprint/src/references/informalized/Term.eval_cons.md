<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: Term.eval_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a term with a leading literal

**Claim.** A term beginning with literal $l$ evaluates at an assignment to the conjunction of the value of $l$ and the evaluation of the remaining term.

**Proof.** Term evaluation applies the list operation “all” to the literal-evaluation predicate. For a list with head $l$ and tail $t$, this operation returns the predicate's value at $l$ conjoined with its value on every element of $t$. These are respectively the evaluation of $l$ and the evaluation of $t$, as claimed.
