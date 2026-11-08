<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.unfoldGate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Unfolded Gate

**Claim.** Under the stated evaluation hypothesis for the assigned circuits, unfolding a well-formed gate at polarity $p$ evaluates to the gate’s value when $p$ is true and to its negation when $p$ is false.

**Proof.** Write the gate as its kind and argument list, and distinguish the gate kind and polarity. For an AND gate at positive polarity, the unfolded node evaluates as the conjunction of the assigned circuits; each child evaluates to the corresponding list value, so this is precisely the gate’s AND evaluation. At negative polarity the unfolded node is an OR of the negated child values, which is the negation of the conjunction. For an OR gate, the positive-polarity unfolding is an OR of the values, while its negative-polarity unfolding is an AND of their negations; these give the OR value and its negation, respectively. The equalities use that tree nodes evaluate by taking the conjunction or disjunction of their children (`BoolCircuit.TreeCircuit.eval_node_true`, `BoolCircuit.TreeCircuit.eval_node_false`), together with the hypothesis on each assigned circuit. Finally, for a NOT gate, well-formedness ensures there is exactly one argument $a$. The unfolding selects the circuit at $a$ with reversed polarity. By the evaluation hypothesis this yields the negation of the argument value at positive polarity and the argument value at negative polarity, exactly the NOT gate’s value and its negation.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_false`, `BoolCircuit.TreeCircuit.eval_node_true`.
