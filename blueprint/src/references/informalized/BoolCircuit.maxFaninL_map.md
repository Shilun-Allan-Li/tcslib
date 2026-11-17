<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.maxFaninL_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Fan-In of a Mapped List

**Claim.** The maximum fan-in of the list obtained by mapping a function over a list is the maximum of the fan-ins of the individual images, with empty-list maximum zero.

**Proof.** Induct on the input list. For the empty list, both sides are zero. For a list with head $a$ and tail $\ell$, the maximum fan-in of the mapped list is the maximum of the fan-in of $f(a)$ and that of the mapped tail, by the head-and-tail formula for list maximum fan-in (`BoolCircuit.TreeCircuit.maxFaninL_cons`). The induction hypothesis identifies the latter with the fold of the individual fan-ins along the tail. This is exactly the head-and-tail decomposition of the fold on the right, proving the equality.

**Key facts.** `BoolCircuit.TreeCircuit.maxFaninL_cons`.
