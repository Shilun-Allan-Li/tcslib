<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.sumSize_map_toBinary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Aggregate Binary Conversion Bound

**Claim.** For a list of circuits in which each binary conversion has size at most three times the original size minus one, the sum of the converted sizes plus the list length is at most three times the sum of the original sizes.

**Proof.** Induct on the list. The empty list has both sides zero. For a nonempty list with head $c$, apply the induction hypothesis to the tail, using the given bound restricted to that tail. The hypothesis also gives $|c^{\mathrm{bin}}|+1\le 3|c|$ for the head. By the sum and length recurrences, the desired inequality is the sum of these two inequalities: the head contributes its converted size and one unit of length, while the tail contributes its corresponding aggregate.

**Key facts.** `BoolCircuit.TreeCircuit.sumSize_nil`, `BoolCircuit.TreeCircuit.sumSize_cons`.
