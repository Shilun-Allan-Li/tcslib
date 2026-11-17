<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFaninL_le_sumSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List maximum fanin bounded by total size

**Claim.** If each circuit in a finite list has maximum fanin at most its size, then the list's maximum fanin is at most the sum of the sizes of its circuits.

**Proof.** Proceed by induction on the list. The empty list has both maximum fanin and total size equal to $0$. For a list with first circuit $c$ and tail $cs$, the hypothesis gives $c$'s fanin at most its size, and also gives the same pointwise bound for every circuit in $cs$. By induction, the maximum fanin of $cs$ is at most its total size. The list maximum is the maximum of $c$'s fanin and the tail maximum (`TreeCircuit.maxFaninL_cons`), while the total size is $c$'s size plus the tail total size (`TreeCircuit.sumSize_cons`). Since both entries of that maximum are at most this sum, the desired bound follows.

**Key facts.** `BoolCircuit.TreeCircuit.maxFaninL_cons`, `BoolCircuit.TreeCircuit.sumSize_cons`.
