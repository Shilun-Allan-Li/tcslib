<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.any_eq_not_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjunction and negated conjunction

**Claim.** If $p(a)=\neg q(a)$ for every element of a list, then the disjunction of $p$ over the list is the negation of the conjunction of $q$ over it.

**Proof.** Induct on the list. The statement holds for the empty list, since its disjunction is false and its conjunction is true. For a head $a$ and tail $l$, use the hypothesis at $a$ and apply the induction hypothesis to the tail. The result reduces to the Boolean identity that $(\neg q(a))\lor\neg A$ equals $\neg(q(a)\land A)$, where $A$ is the tail conjunction. This identity holds for either Boolean value of $q(a)$.
