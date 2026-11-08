<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.all_eq_not_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Test and Negated Existential Test

**Claim.** If $p(a)=
eg q(a)$ for every entry $a$ of a list, then every entry satisfies $p$ exactly when no entry satisfies $q$.

**Proof.** Induct on the list. For the empty list, the universal test and the negation of the existential test are both true. For a head $a$ and tail $l$, the induction hypothesis applies to the tail because the given pointwise relation restricts to its entries. At the head, split according to whether $q(a)$ is false or true. In either case, $p(a)=
eg q(a)$ makes the head contribution to the universal test equal to the negation of the head contribution to the existential test; combining this with the tail equivalence gives the result for the whole list.
