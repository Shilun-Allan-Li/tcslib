<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.maxFaninL_map_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In Bound Under Mapping

**Claim.** If every image of an element in a list has maximum fan-in at most $m$, then the maximum fan-in across the mapped list is at most $m$, with empty-list maximum zero.

**Proof.** Use induction on the list. The empty-list maximum is zero and hence at most $m$. For a head $c$ and tail, the hypothesis gives a bound of $m$ for the image of the head and for every image from the tail. Applying the induction hypothesis bounds the tail’s maximum fan-in by $m$. The maximum for the mapped list is the maximum of the head’s fan-in and the tail’s maximum, by `BoolCircuit.TreeCircuit.maxFaninL_cons`; since both are at most $m$, so is their maximum.

**Key facts.** `BoolCircuit.TreeCircuit.maxFaninL_cons`.
