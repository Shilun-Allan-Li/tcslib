<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.size_unfoldGate_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for an unfolded gate

**Claim.** Under the stated well-formedness and polarity-size hypotheses, the size of the circuit obtained by unfolding $g$ at either polarity $p$ is at most one plus the sum of the sizes assigned to its arguments at polarity $p$.

**Proof.** Consider the three gate kinds. For an AND gate, unfolding produces a node whose children are the assigned circuits at polarity $p$; the node-size formula (BoolCircuit.TreeCircuit.size_node), followed by the identity expressing the sum of mapped circuit sizes as the list sum (BoolCircuit.sumSize_map), gives the bound with equality. For an OR gate the same computation applies: although the node label changes with the polarity, its size is still one plus the sum of the child sizes. For a NOT gate, well-formedness says its argument list has length one, so it consists of a single vertex $a$. Unfolding returns the circuit assigned to $a$ at the opposite polarity. The hypothesis that assigned circuits have equal size at both polarities identifies its size with that at $p$. The right-hand side is one plus that same size, which proves the inequality.

**Key facts.** `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.sumSize_map`.
