<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.prefixTruth_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth of Concatenated Quantifier Prefixes

**Claim.** Truth of a concatenated prefix $q$ followed by $r$ is equivalent to truth of $q$ with the predicate that $r$ is true starting at index $i+|q|$.

**Proof.** Induct on the prefix $q$. For the empty prefix, both sides reduce to truth of $r$ under the same assignment and at the same index. For a nonempty prefix, write it as a first quantifier followed by a shorter prefix. Advancing past that first quantifier changes the starting index from $i$ to $i+1$, and the shorter prefix then advances it by its length. This total index is $i+|q|$. If the first quantifier is existential, the equivalence follows by applying the induction hypothesis for each possible chosen bit and preserving the existential quantifier. If it is universal, apply the same reasoning for each bit under the universal quantifier.
