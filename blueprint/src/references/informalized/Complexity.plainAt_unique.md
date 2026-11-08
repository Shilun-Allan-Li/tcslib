<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.plainAt_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of a plain suffix

**Claim.** If $u$ and $u'$ each agree with the segment of $x$ beginning at position $r$ and each satisfies the required length condition, then $u=u'$.

**Proof.** Apply the characterization of a plain segment (plainAt_iff) to each hypothesis. Both identify the corresponding word with the list obtained by deleting the first $r$ entries of $x$. Hence $u$ and $u'$ are equal.

**Key facts.** `Complexity.plainAt_iff`.
