<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combineFuel_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserved by Recursive Combination

**Claim.** For every fuel value, recursively combining a list of Boolean circuit trees with a chosen AND or OR gate has the same evaluation as applying that gate directly to the list under the given assignment.

**Proof.** Proceed by induction on the fuel and split according to the list shape. With zero fuel, the recursive construction is exactly the single gate on the original list. With positive fuel and an empty list, it is again that gate; with a singleton list, it returns the only circuit, whose value agrees with the corresponding one-input AND or OR. For a list with at least two entries, the construction recursively combines the list obtained by pairing consecutive circuits. The induction hypothesis says that this recursive result evaluates as the gate applied to the paired list. Pairing preserves the evaluation of the gate applied to the whole list (`eval_node_pairUp`): each new binary gate evaluates as the same gate on its two inputs, and associativity of Boolean conjunction or disjunction allows the fold to retain its value. Thus the recursive combination and the original gate have equal evaluations.

**Key facts.** `BoolCircuit.eval_node_pairUp`.
