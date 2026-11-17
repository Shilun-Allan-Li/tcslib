<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.truthAux_iff_prefixTruth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth of a Quantified Prefix

**Claim.** Recursively evaluating a quantified prefix on the formula is equivalent to applying that same prefix to the predicate that the formula evaluates to true.

**Proof.** Induct on the list of quantifiers, with the assignment and starting index arbitrary. For the empty list, both sides assert directly that the formula evaluates to true. If the first quantifier is existential, both definitions assert that there is a Boolean value for the current variable such that the remaining prefix holds; the induction hypothesis identifies the two remaining-prefix assertions for each choice. If the first quantifier is universal, the same reasoning applies to every Boolean value.
