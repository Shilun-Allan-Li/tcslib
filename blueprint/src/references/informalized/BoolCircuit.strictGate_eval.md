<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.strictGate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a strictified gate

**Claim.** Under the stated true and false values at the two added vertices, and agreement between shifted original inputs and their old values, strictification preserves the gate’s evaluation.

**Proof.** Use the hypotheses that the gate is well formed and has at most two inputs, then consider its kind and input-list length. For an empty AND or OR gate, strictification switches the connective and uses the two added vertices; their values, true at $n+1$ and false at $n+2$, give the same empty-conjunction or empty-disjunction value as before. For a one-input AND or OR gate, the added true or false input leaves the original input’s value unchanged, and the assumed correspondence identifies that value with the original evaluation. A NOT gate has exactly one input by well-formedness; its shifted input has the corresponding value, so negating it preserves the evaluation. In the remaining allowed cases there are two inputs and the gate is AND or OR; both shifted inputs have their corresponding old values, so applying the same connective gives equal results.
