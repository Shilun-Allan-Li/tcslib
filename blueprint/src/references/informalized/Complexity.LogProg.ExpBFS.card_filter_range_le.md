<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.card_filter_range_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtered Initial Interval Bound

**Claim.** For every natural number $K$ and decidable predicate $p$, at most $K$ elements of $[0,K)$ satisfy $p$.

**Proof.** Filtering a finite set cannot increase its cardinality, so the filtered range has cardinality at most that of the range. The range $[0,K)$ has exactly $K$ elements, giving the bound.
