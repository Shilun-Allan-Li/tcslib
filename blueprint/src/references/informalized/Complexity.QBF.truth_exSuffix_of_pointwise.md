<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.truth_exSuffix_of_pointwise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Suffix After a Quantified Prefix

**Claim.** Under the stated variable-count and pointwise hypotheses, truth of the formula with prefix $q$ followed by $G$ existential quantifiers is equivalent to applying prefix $q$ to $P$, from the all-false assignment at index $0$.

**Proof.** First identify recursive formula truth with prefix truth for the predicate that the matrix evaluates to true (truthAux_iff_prefixTruth). Decomposing the combined prefix into $q$ followed by the existential suffix expresses the result as prefix $q$ applied to the predicate that the suffix is true, starting at index $|q|$ (prefixTruth_append). For any assignment reached after $q$, the variable-count bound and the existential-completion theorem identify that suffix predicate with the existence of a satisfying assignment agreeing below $|q|$ (truthAux_exSuffix_iff). By the pointwise hypothesis, this is precisely $P$ of the reached assignment. Replacing the predicate inside prefix $q$ by this equivalent predicate preserves prefix truth (prefixTruth_congr), giving the claimed equivalence.

**Key facts.** `Complexity.QBF.truthAux_iff_prefixTruth`, `Complexity.QBF.prefixTruth_append`, `Complexity.QBF.truthAux_exSuffix_iff`, `Complexity.QBF.prefixTruth_congr`.
