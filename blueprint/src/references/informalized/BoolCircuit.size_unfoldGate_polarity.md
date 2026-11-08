<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.size_unfoldGate_polarity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarity independence of unfolded size

**Claim.** If each vertex's assigned circuit has the same size at both polarities, then unfolding any gate at either polarity gives trees of equal size.

**Proof.** For an AND gate, the unfolded circuit is a node, whose size is one plus the sum of its children's sizes by the node-size formula (BoolCircuit.TreeCircuit.size_node). Expressing this as the sum of the sizes of the assigned circuits along the argument list uses the mapped-sum identity (BoolCircuit.sumSize_map). Each summand agrees at polarities $p$ and $q$ by hypothesis, so the total sizes agree. The OR case has the same argument: its node label may vary with polarity, but the size formula depends only on its children, whose sizes agree term by term. For a NOT gate, unfolding selects the assigned circuit at the head argument and opposite polarity; the hypothesis directly equates that circuit's size at the two opposite polarities arising from $p$ and $q$.

**Key facts.** `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.sumSize_map`.
