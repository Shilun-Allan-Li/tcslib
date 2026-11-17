<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.gateClauses_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of Gate Clauses

**Claim.** For every assignment $u$, Boolean value $b$, and list $cs$ of circuit trees, the assignment that gives inputs their values under $u$ and gates their evaluated values satisfies every associated gate clause.

**Proof.** Consider each value of $b$ and each clause in the resulting formula. When $b$ is false, the distinguished clause is satisfied either by the positive literal for a child evaluating to true, which exists by the characterization of a false-labelled node (eval_node_false_iff), or, if the node evaluates to false, by its negative literal. Each two-literal clause is satisfied either by the node’s positive literal when the node evaluates to true, or by the child’s negative literal when that child evaluates to false; the former case uses the same characterization. When $b$ is true, the distinguished clause is satisfied by the node’s positive literal if the node evaluates to true. Otherwise some child evaluates to false, since a true-labelled node evaluates to true exactly when all its children do (eval_node_true_iff), and that child’s negative literal satisfies the clause. For each two-literal clause, if the node evaluates to true then every child does, so the child’s positive literal satisfies it; if the node evaluates to false then its negative literal satisfies it. These cases cover all clauses.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_false_iff`, `BoolCircuit.TreeCircuit.eval_node_true_iff`.
