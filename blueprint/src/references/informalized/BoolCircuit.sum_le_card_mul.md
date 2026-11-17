<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.sum_le_card_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Bound on a Finite Sum

**Claim.** If every value of $f$ on a finite list of natural numbers is at most $B$, then the sum of those values, with repetitions counted, is at most the list length times $B$.

**Proof.** Induct on the list. The empty case is immediate. For a head $a$ and tail $l$, the sum and length recurrences reduce the claim to $f(a)+\sum_{b\in l}f(b)\le B+|l|B$. The hypothesis bounds the head by $B$ and, restricted to the tail, the induction hypothesis bounds its sum by $|l|B$. Adding these inequalities gives the result.
