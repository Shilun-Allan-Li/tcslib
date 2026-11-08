<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.whileVariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Termination by a decreasing variant

**Claim.** If the invariant is initially true, the guard is safe under the invariant, every true-guard body execution preserves the invariant and strictly decreases the natural-valued measure, and false-guard states satisfying the invariant satisfy $Q$, then the loop ends within the stated variant-based time bound.

**Proof.** First prove by induction on a natural number $n$ that, whenever $I$ holds and $m(\sigma)\le n$, the loop ends within $m(\sigma)(c.cost+1+b)+(c.cost+1)$. At measure zero, the guard cannot be true: if it were, the body execution would produce a natural number strictly smaller than zero. So the guard is false, and the false-guard loop rule gives termination and $Q$. At a successor bound, split on whether the guard holds. If it is false, the same rule finishes immediately. If it is true, execute the body; its endpoint satisfies $I$ and has a strictly smaller measure. Apply the induction hypothesis there, and combine the body and subsequent loop executions with the true-guard rule. The strict decrease implies that the subsequent loop's bound plus one iteration's cost fits within the original measure-based bound. Finally, apply this result with $n=m(\sigma)$ and enlarge the time bound using `Ends.mono` and the assumed inequality.

**Key facts.** `Light.Ends.mono`.
