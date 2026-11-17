<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: DNF.eval_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Constructed DNF

**Claim.** The DNF whose terms are $ts$ evaluates to true at an assignment $x$ exactly when at least one term in $ts$ evaluates to true at $x$.

**Proof.** Unfolding the evaluation of the constructed formula identifies its terms with $ts$. Its evaluation is therefore precisely the list operation that returns true when some term in $ts$ evaluates to true at $x$.
