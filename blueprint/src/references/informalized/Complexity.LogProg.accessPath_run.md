<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessPath_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Runs from Access Paths

**Claim.** For either access mode, an access path from a configuration $c$ on input $y$ to a configuration $c'$ yields a time $T$ at which the run from $c$ reaches $c'$, with every earlier configuration satisfying the work-head bounds.

**Proof.** Induct on the finite access path. For a path of length zero, take $T=0$: the run is at its initial configuration, and there are no times $t<0$ to check. For the extension of a path by one step, suppose the preceding path reaches its endpoint at time $n$ and all configurations at times below $n$ are safe. Take $T=n+1$. The run recurrence says that its configuration at time $n+1$ is the result of one step from the time-$n$ configuration; by the induction hypothesis this is the preceding endpoint, and the path’s final edge identifies its successor with $c'$. If $t<n+1$, then either $t<n$, when safety follows from the induction hypothesis, or $t=n$, when the edge hypothesis supplies safety of the preceding endpoint. Thus every time strictly before $T$ is safe.

**Key facts.** `Complexity.LogProg.rrun_succ`.
