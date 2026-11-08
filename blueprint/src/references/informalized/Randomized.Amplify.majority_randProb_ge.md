<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.majority_randProb_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Amplification Bound

**Claim.** If the probability that the machine outputs the one-symbol word $[v]$ after $T$ random choice bits is at least $\frac12+\varepsilon$, then the probability that the majority of $2n+1$ blocks yields $v$ is at least $1-2(1-4\varepsilon^2)^n$.

**Proof.** We bound the probability that the majority is wrong. The tail estimate for block counts (`randProb_tail_le`) says that if a Boolean test is true with probability at most $\frac12-\varepsilon$ on one block, then among $2n+1$ independent blocks the probability that at least half test true is at most $2(1-4\varepsilon^2)^n$; here $(2n+1)/2$ in its exponent simplifies to $n$.

The test that a block accepts, namely that the machine outputs $[\mathrm{true}]$, has probability exactly $N.outputProb(x,T,[\mathrm{true}])$ (`randProb_congr`). If $v=\mathrm{false}$, the assumed lower bound on the probability of output $[\mathrm{false}]$, together with disjointness of the two one-symbol outputs and the fact that total probability is at most one (`randProb_or_disjoint`, `randProb_le_one`), implies that acceptance has probability at most $\frac12-\varepsilon$. Apply the tail estimate to acceptance. The event that the majority rule returns false is contained in the event that at least half the blocks accept, so its probability is at most the same tail bound (`randProb_mono`). Taking complements (`randProb_not`) gives the desired success bound.

If $v=\mathrm{true}$, the probability that a block rejects is at most $\frac12-\varepsilon$: this follows by complementing the acceptance probability (`randProb_bool_false`) and using the hypothesis. Apply the tail estimate to rejection. By the exact relation between the count of accepting and rejecting blocks (`blockCount_add_not`), a majority outcome other than true forces at least half the blocks to reject. Monotonicity of probability then bounds the failure probability by the tail estimate, and complementing again gives the claimed lower bound.

**Key facts.** `Randomized.randProb_tail_le`, `Randomized.randProb_congr`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_le_one`, `Randomized.randProb_mono`, `Randomized.randProb_not`, `Randomized.randProb_bool_false`, `Randomized.blockCount_add_not`.
