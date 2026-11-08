<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.length_le_sumSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List Length Bounded by Total Circuit Size

**Claim.** For every finite list of circuit trees, its length is at most the sum of the sizes of its circuits.

**Proof.** Proceed by induction on the list. The empty list has length and total size both zero. For a list with head $c$ and tail $cs$, the induction hypothesis gives $cs.length \leq \mathrm{sumSize}(cs)$, and every circuit has size at least one (`BoolCircuit.TreeCircuit.one_le_size`). The total size of the cons list is $c.size+\mathrm{sumSize}(cs)$ (`BoolCircuit.TreeCircuit.sumSize_cons`), while its length is one more than the tail length. Combining these inequalities gives the claimed bound.

**Key facts.** `BoolCircuit.TreeCircuit.one_le_size`, `BoolCircuit.TreeCircuit.sumSize_cons`.
