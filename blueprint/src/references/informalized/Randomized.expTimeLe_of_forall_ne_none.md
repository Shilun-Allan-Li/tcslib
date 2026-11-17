<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.expTimeLe_of_forall_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected time bound from eventual halting

**Claim.** If $r$ is prefix-stable and returns a value on every Boolean list of length $t_0$, then for every $K$ the sum of the probabilities that $r$ has not halted by time $s$, over $s<K$, is at most $t_0$.

**Proof.** 1. First show that the probability of not having halted is zero at every time $s\ge t_0$. If a length-$s$ word were an input on which $r$ returns none, its prefix of length $t_0$ would also return none: otherwise prefix stability would force the longer word to return the same value. This contradicts the hypothesis that every word of length $t_0$ returns a value. The event of nonhalting at time $s$ is therefore empty, so its probability is zero. This uses the prefix-stability consequence that a nonhalting word has nonhalting prefixes (`Randomized.IsPrefixStable.take_eq_none`), together with invariance of the random-word probability under replacing equivalent events (`Randomized.randProb_congr`) and the zero probability of the empty event (`Randomized.randProb_false`).

2. For each $K$, induct on $K$ to bound the partial sum by $\min(K,t_0)$. The claim is immediate at $K=0$. On passing from $K$ to $K+1$, if $K<t_0$, the new summand is at most $1$, so the sum increases by at most one, matching the increase of the minimum. If $K\ge t_0$, the new summand is zero by the first step, and the minimum remains $t_0$. The probability bound used in the first case is `Randomized.notHaltedProb_le_one`. Since $\min(K,t_0)\le t_0$, the desired bound follows.

**Key facts.** `Randomized.IsPrefixStable.take_eq_none`, `Randomized.randProb_congr`, `Randomized.randProb_false`, `Randomized.notHaltedProb_le_one`.
