<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.val_leaf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation at the Prefix Leaf

**Claim.** At depth equal to the length of the prefix, the valuation predicate is equivalent to the matrix evaluating to true under the assignment encoded by $S$ at that depth.

**Proof.** At depth $|q|$, dropping the prefix leaves the empty list. The recursive definition of quantified truth on an empty quantifier list is exactly that the matrix evaluates to true under the given assignment. Substituting the definition of the valuation predicate therefore gives the claimed equivalence.
