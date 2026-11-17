<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean :: Complexity.Codec.icCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Increment Counts

**Claim.** For every increment-count identifier $c$, its associated count is at most $4W$, where $W=H+3k+1$.

**Proof.** Check the five possible identifiers. For $E$ and $E2$, the count is $2W$, which is at most $4W$. For $U$ and $U2$, the count is $4$, and $W\ge1$, so $4\le4W$. For $C$, the count is $2(H+2)$; since $W=H+3k+1\ge H+1$, we have $2(H+2)\le4W$. These cases establish the bound for every identifier.
