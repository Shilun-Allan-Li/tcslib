<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Comparator Reaches Its Verdict

**Claim.** Given a bound $W$ on the lengths of four Boolean words, the comparator reaches a completed control by time $2W+2$, carrying the truth value of equality between the sum of the first two word values and the sum of the last two. It has not reached a completed control at any earlier time, and at the selected completion time the original words remain intact and all work-tape heads are at zero.

**Proof.** Let $m$ be the maximum of the four lengths, and let $b$ be the verdict computed by the scan state after $m$ columns. The comparator's run theorem says that at time $2m+2$ it is in the completed control carrying $b$, with the original words and all heads at zero (`Complexity.clCmp_run`). The bound on each word length gives $m\le W$, so this time is at most $2W+2$. Choose the first time $t$ at or before $2m+2$ when the run is in a completed control carrying this same $b$. Such a time exists by the run theorem, and it is positive because at time zero the machine is in its initial scanning control. The verdict specification identifies $b$ with equality of the two sums (`Complexity.clCmpVerdict_spec`).

It remains to show that no earlier time is in any completed control and that the run at $t$ has the stated full configuration. Suppose an earlier configuration at time $j<t$ were completed with verdict $d$. Completed configurations are fixed by one step (`Complexity.clCmp_idle`), so iterating from time $j$ keeps that configuration fixed through time $2m+2$. Runs compose by addition of their lengths (`Turing.MultiTapeTM.runFrom_add`), hence the configuration at time $2m+2$ would also be completed with verdict $d$. Comparing it with the run theorem's configuration forces $d=b$. Then the run would already have reached the completed control carrying $b$ at time $j$, contradicting the choice of $t$ as the first such time. Finally, the configuration at time $t$ is fixed by the same idle property; iterating to time $2m+2$ and using the run theorem shows that the entire configuration at time $t$ equals the claimed one. The zero-time run identity is used to rule out $t=0$ (`Turing.MultiTapeTM.runFrom_zero`).

**Key facts.** `Complexity.clCmp_run`, `Complexity.clCmpVerdict_spec`, `Complexity.clCmp_idle`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_zero`.
