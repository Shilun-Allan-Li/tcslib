<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.sumSize_pairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing Does Not Increase Aggregate Size

**Claim.** Pairing a list of circuits leaves the sum of circuit sizes plus list length no greater than its original value.

**Proof.** Proceed by cases on the list. The empty list and a singleton are unchanged by pairing, so the bound is equality. For a list beginning $c_1,c_2$, the construction replaces those two entries by one node with children $c_1,c_2$, followed by the recursively paired remainder. The node has size $1+|c_1|+|c_2|$. Thus the replacement's size plus its one list entry is $2+|c_1|+|c_2|$, whereas the original two entries contribute $|c_1|+|c_2|+2$. These contributions agree; applying the induction hypothesis to the remainder proves the result.

**Key facts.** `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.TreeCircuit.sumSize_cons`, `BoolCircuit.TreeCircuit.sumSize_nil`.
