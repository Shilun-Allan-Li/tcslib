<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.hitProb_mk_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting-Probability Recurrence

**Claim.** For distinct vertices $s,t$ in the digraph on $\mathrm{Fin}(n)$ defined by $r$, if $s$ has at least one outgoing neighbor, then the probability of hitting $t$ from $s$ after $k+1$ steps is the average of the $k$-step probabilities over all outgoing neighbors of $s$.

**Proof.** Since $s\ne t$, the successor-time definition does not assign probability $1$ immediately at $s$; it uses the outgoing-neighbor average. The positive cardinality assumption ensures that the neighbor set is nonempty, so this average is the sum of the $k$-step hitting probabilities over those neighbors divided by their number, as claimed.
