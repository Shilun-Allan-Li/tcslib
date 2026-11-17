<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.badPairSubtype_card_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Incorrect Input Pairs

**Claim.** The number of pairs $(x,i)$ on which the protocol disagrees with the Index function equals the sum over strings $x$ of the number of coordinates on which the protocol disagrees with the corresponding bit of $x$.

**Proof.** Group the incorrect pairs by their first coordinate $x$. For each fixed string $x$, the indices in its group are exactly those for which the protocol's output differs from the $i$th bit of $x$; these form the mismatch subtype for $x$. The incorrect-pair subtype is thus in bijection with the dependent sum of these mismatch subtypes over all $x$. Counting that disjoint union gives the sum of the cardinalities of its fibers, as asserted.
