<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.not_altQuant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementing Alternating Quantifiers

**Claim.** Negating the $k$-level alternating quantifier condition for $V$ is equivalent to the condition for the complement of $V$ with the initial quantifier switched.

**Proof.** Proceed by induction on the number of quantifier levels, simultaneously for both choices of the initial quantifier and every input string. At level zero the condition is membership in $V$, so its negation is membership in the complement, as required. At a successor level, use the characterizations of an existential first level and a universal first level (the facts `altQuant_true_succ` and `altQuant_false_succ`). If the first quantifier is existential, its negation says that every length-$m$ witness fails the remaining condition. Apply the induction hypothesis to each such witness: failure of the remaining condition is precisely the complementary condition with its initial quantifier switched. This gives the universal condition on the right. If the first quantifier is universal, its negation says there is a length-$m$ string for which the remaining condition fails. The induction hypothesis turns that failure into the complementary condition, yielding the existential condition on the right. The pair encoding of the input and quantified string is unchanged throughout.

**Key facts.** `Complexity.altQuant_true_succ`, `Complexity.altQuant_false_succ`.
