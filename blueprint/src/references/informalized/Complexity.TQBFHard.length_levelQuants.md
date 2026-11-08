<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.length_levelQuants -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the level quantifier list

**Claim.** For natural numbers $w$ and $r$, the list of quantifiers at width $w$ and depth $r$ has length $3wr$.

**Proof.** Induct on $r$. At depth zero the list is empty, so both sides are zero. At successor depth, the definition places three lists of $w$ repeated quantifiers before the list at depth $r$. Their total length is $3w$, and by induction the remaining list has length $3wr$. Thus the new length is $3w+3wr=3w(r+1)$; the equality is ordinary arithmetic.
