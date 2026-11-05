<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.max_influence_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Some Coordinate Attains the Average Influence

**Claim.** Let $f:\{0,1\}^n\to\mathbb{R}$ be a Boolean function on the hypercube of dimension $n\ge 1$, let $\mathrm{Inf}_i[f]$ denote the influence of the $i$-th coordinate, and let $I[f]=\sum_{j=1}^{n}\mathrm{Inf}_j[f]$ be the total influence. Then at least one coordinate carries influence no smaller than the average: there is an index $i$ with $\mathrm{Inf}_i[f]\ge I[f]/n$.

**Proof.** This is the elementary "a maximum is at least the mean" principle, and the Lean proof records exactly that averaging argument, run by contradiction.

Suppose, for contradiction, that *no* coordinate reaches the average, i.e. that for every index $i$ we have the strict inequality
\[
  \mathrm{Inf}_i[f] \;<\; \frac{I[f]}{n}.
\]
(This is the negation of the claim: the existential "$\mathrm{Inf}_i[f]\ge I[f]/n$ for some $i$" becomes "$\mathrm{Inf}_i[f] < I[f]/n$ for all $i$".)

Now sum this inequality over all $n$ coordinates. The left-hand side is, by definition of total influence, $I[f]=\sum_{i=1}^n \mathrm{Inf}_i[f]$. The right-hand side is a sum of $n$ copies of the constant $I[f]/n$. The decisive point is that summing a *strict* termwise inequality over an index set gives a strict inequality of the sums — and this requires the index set to be nonempty (`Finset.sum_lt_sum_of_nonempty`), which is exactly where the hypothesis $n\ge 1$ enters: over an empty index set both sides would be $0$ and strictness would fail. Since $n\ge 1$ the coordinate set $\{1,\dots,n\}$ is nonempty, so
\[
  I[f] \;=\; \sum_{i=1}^n \mathrm{Inf}_i[f] \;<\; \sum_{i=1}^n \frac{I[f]}{n} \;=\; n\cdot\frac{I[f]}{n} \;=\; I[f].
\]
The two equalities on the right are pure bookkeeping: a constant summed $n$ times is $n$ times the constant, and the factor of $n$ cancels the denominator (legitimate because $n\ne 0$, again by $n\ge 1$). We have derived $I[f] < I[f]$, which is impossible.

This contradiction refutes the assumption that every coordinate lies strictly below the average, so some coordinate must satisfy $\mathrm{Inf}_i[f]\ge I[f]/n$, as claimed. Note that the argument is purely formal in the inequalities and never uses the sign or magnitude of the influences, so it holds for an arbitrary real-valued $f$.
