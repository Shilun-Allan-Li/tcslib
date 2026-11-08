<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.DAGCircuit.sum_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total gate-cost bound

**Claim.** If every gate has at most size$(C)$ arguments, then the sum of the number of arguments plus two over all gates is at most the number of gates times size$(C)+2$.

**Proof.** Proceed by induction on the list of gates, writing it as $g::G$ in the inductive step. The sum for this list is the cost of $g$ plus the sum for $G$. The hypothesis bounds the first cost by size$(C)+2$, and it applies to every gate of $G$ as well, so the induction hypothesis bounds the remaining sum by $|G|(\mathrm{size}(C)+2)$. Adding these bounds gives $(|G|+1)(\mathrm{size}(C)+2)$, as required. For the empty list, both the sum and the gate count are zero.
