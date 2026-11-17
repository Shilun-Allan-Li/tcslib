<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.expTimeLe_repeatRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected runtime of repeated runs

**Claim.** If a run on a uniformly random block of $t>0$ bits fails to halt with probability at most $1/2$, then repeatedly running it on successive blocks has, for every cutoff $K$, a sum of nonhalting probabilities over times $s<K$ bounded by $2t$.

**Proof.** 1. Write $a$ for the probability that one block fails to halt. By assumption $0\le a\le 1/2$. After $m$ complete blocks, failure to halt has probability $a^m$, and this probability is unchanged during each of the next $t$ positions, before the following block is complete (`Randomized.notHaltedProb_repeatRun`). Consequently, summing over the first $nt$ times gives $t\sum_{j<n}a^j$. This identity follows by induction on $n$: each added block contributes $t$ copies of $a^n$.

2. The geometric sum $\sum_{j<K}a^j$ is at most $2$, since $0\le a\le 1/2<1$. For an arbitrary cutoff $K$, extend the sum of nonhalting probabilities to the first $Kt$ times; all added terms are nonnegative (`Randomized.notHaltedProb_nonneg`). The block identity then bounds the extended sum by $t\cdot 2=2t$. The nonnegativity of $a$ also follows from nonnegativity of uniform-event probabilities (`Randomized.randProb_nonneg`).

**Key facts.** `Randomized.randProb_nonneg`, `Randomized.notHaltedProb_repeatRun`, `Randomized.notHaltedProb_nonneg`.
