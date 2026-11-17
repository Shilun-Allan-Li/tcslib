<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.any_congr_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of list disjunction

**Claim.** If two Boolean-valued predicates agree at every element of a list, then their listwise disjunctions over that list agree.

**Proof.** Induct on the list. For the empty list, both disjunctions are false. For a list with head $a$ and tail $l$, its disjunction is the disjunction of the predicate at $a$ with the disjunction over $l$. The hypotheses give agreement at $a`, and their restriction to the tail gives the induction hypothesis. Thus the two head values and the two tail disjunctions agree, so the full disjunctions agree.
