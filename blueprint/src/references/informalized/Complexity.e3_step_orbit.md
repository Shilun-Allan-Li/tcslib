<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_step_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary search orbit

**Claim.** For every binary string $w$ and every $i\le |w|+1$, iterating the search round $i$ times from the empty string gives the string of $i$ ones.

**Proof.** Induct on $i$. At $i=0$, no round has been applied, so the result is the empty string, which is the list of zero ones. For the successor step, suppose the claim holds at $i$ and $i+1\le |w|+1$. Then $i\le |w|$, so the current string of $i$ ones has length at most $|w|$; the next round appends one more $1$. The result is therefore the list of $i+1$ ones.
