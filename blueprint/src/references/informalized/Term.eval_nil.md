<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: Term.eval_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the empty term

**Claim.** For every natural number $n$ and Boolean assignment $x : \mathrm{Fin}(n) \to \{\mathrm{false},\mathrm{true}\}$, the empty term evaluates to true.

**Proof.** The evaluation of a term is the conjunction of the evaluations of its literals. The empty list has no literals to check, so its universal condition is true; hence the empty term evaluates to true.
