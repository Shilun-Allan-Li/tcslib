<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.qStep_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer of one quantified step

**Claim.** If $d$ sends length-$B$ words to length-$m$ words, is surjective on those words, and $Q'(v)$ is equivalent to $Q(d(v))$ for every length-$B$ word, then the corresponding existential or universal statements at lengths $B$ and $m$ are equivalent.

**Proof.** Split on the quantifier type. For the existential case, a length-$B$ witness for $Q'$ decodes to a length-$m$ witness for $Q$, using the length and predicate hypotheses. Conversely, take a length-$m$ witness for $Q$ and use surjectivity to choose a length-$B$ preimage; the predicate equivalence makes it a witness for $Q'$. For the universal case, assume first that every length-$B$ word satisfies $Q'$. Given any length-$m$ word, surjectivity supplies a length-$B$ preimage, and the predicate equivalence transfers its truth to the given word. In the reverse direction, assume every length-$m$ word satisfies $Q$. For any length-$B$ word, its image has length $m$, so the universal assumption applies to that image; predicate equivalence then gives $Q'$ on the original word.
