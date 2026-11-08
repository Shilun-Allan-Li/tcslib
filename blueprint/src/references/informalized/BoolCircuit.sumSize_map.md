<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.sumSize_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size sum of a mapped list

**Claim.** The sum of the sizes of the circuits obtained by mapping a function over a list equals the sum of the sizes in the mapped list.

**Proof.** Induct on the list. For the empty list both sums are zero. For a head $a$ and tail $l$, the mapped list has head $f(a)$ and tail $l.map f$. The sum-size decomposition (`TreeCircuit.sumSize_cons`) expresses its size sum as $(f(a)).size$ plus the tail sum; the ordinary list sum has the same decomposition. The induction hypothesis identifies the tail sums, proving the equality.

**Key facts.** `BoolCircuit.TreeCircuit.sumSize_cons`.
