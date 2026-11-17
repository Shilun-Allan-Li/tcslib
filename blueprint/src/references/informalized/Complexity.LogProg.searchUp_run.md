<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.searchUp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ascending Search Reaches the First Positive Test

**Claim.** Starting at a value $c_0\le c$ with no positive test between $c_0$ and $c$, successive increments reach the test at $c$, which enters $\mathrm{yes}$. Every configuration before the final one satisfies the precondition and the register bound.

**Proof.** Induct on $k=c-c_0$. If $k=0$, then $c_0=c$. The test state satisfies the precondition by assumption, and its updated valuation is bounded by $B$ because $c\le B$. The test hypothesis and $P(c)$ take one step to the desired $\mathrm{yes}$ configuration, so the remaining reachability is reflexive. If $k>0$, the minimality assumption gives $\neg P(c_0)$. The test at $c_0$ therefore enters $\mathrm{inc}$ without changing the valuation. The increment instruction then raises register $r$ to $c_0+1$ and returns to $\mathrm{test}$. The test configuration is guarded by the assumed precondition, and both valuations remain bounded by $B$, since they are updates at values no greater than $c$. Apply the induction hypothesis starting from $c_0+1$; the distance to $c$ has decreased by one and the no-earlier-positive condition persists. Prepending the two steps gives the required run.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`.
