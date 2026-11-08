<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: CNF.eval_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a constructed CNF

**Claim.** The CNF formed from a list of clauses evaluates to true on an input exactly when every clause in the list evaluates to true on that input.

**Proof.** The constructed formula stores the given list as its clauses, and CNF evaluation is defined as the conjunction of the evaluations of those clauses. Therefore its value is precisely the list's universal conjunction of clause values.
