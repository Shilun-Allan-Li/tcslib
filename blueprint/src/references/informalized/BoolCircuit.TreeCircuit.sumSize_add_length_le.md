<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.sumSize_add_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a List of Circuit Sizes

**Claim.** If every circuit $c$ in a finite list $cs$ satisfies $\mathrm{size}(c)+1\le m$, then the sum of their sizes plus the list length is at most the list length multiplied by $m$.

**Proof.** Induct on the list. For the empty list, both the sum of sizes and the length are zero. For a list consisting of $c$ followed by a tail, the induction hypothesis bounds the tail's total size plus its length by its length times $m$. The assumption gives $\mathrm{size}(c)+1\le m$. Adding these bounds and using that the full list has one more element than its tail proves the stated inequality.

**Key facts.** `BoolCircuit.TreeCircuit.sumSize_nil`, `BoolCircuit.TreeCircuit.sumSize_cons`.
