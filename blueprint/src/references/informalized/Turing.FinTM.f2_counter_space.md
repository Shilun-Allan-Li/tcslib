<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Space Bound

**Claim.** For every Boolean list $x$ and natural time $t$, the counter machine visits at most $5(\mathrm{size}(|x|)+1)$ distinct work-tape cells through time $t$.

**Proof.** For the sole work tape, each visited position lies in the interval from $-2(\mathrm{size}(|x|)+1)$ to $2(\mathrm{size}(|x|)+1)$ by the head-position bound (`f2_counter_heads`). Thus the set of visited cells is contained in that integer interval. An interval of integers with endpoints $-2m$ and $2m$ has $4m+1$ elements, where $m=\mathrm{size}(|x|)+1$; this is at most $5m$. Therefore the number of distinct visited cells satisfies the claimed bound. The machine has just one work tape, so this is also the total space used.

**Key facts.** `Turing.FinTM.f2_counter_heads`.
