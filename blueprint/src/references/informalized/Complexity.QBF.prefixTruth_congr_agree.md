<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.prefixTruth_congr_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Initial-Segment Agreement

**Claim.** If two predicates agree on every assignment matching the given assignment below index $i$, then truth of any finite quantifier prefix at that assignment and index is equivalent for the two predicates.

**Proof.** Induct on the quantifier prefix, allowing the assignment and starting index to vary. With an empty prefix, the claim is exactly the assumed agreement applied to the given assignment, which matches itself below $i$. For a first quantifier at index $i$, consider any bit $b$ assigned there. An assignment matching the updated assignment below $i+1$ also matches the original assignment below $i$: below $i$, the update leaves values unchanged, and the new index $i$ is not in that initial segment. Thus the predicate agreement hypothesis applies to every assignment relevant to the remaining prefix. The induction hypothesis gives equivalence for that remainder, for each bit $b$. Preserving the existential quantifier yields the result when the first quantifier is existential; preserving the universal quantifier yields it when the first quantifier is universal.
