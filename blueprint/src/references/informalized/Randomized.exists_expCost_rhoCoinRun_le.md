<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.exists_expCost_rhoCoinRun_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Weighted Nonhalting Cost Bound

**Claim.** For every natural number $c$, there is a rational constant $C$ that bounds, uniformly in the bit sequence $p$ and cutoff $K$, the sum of $(t+1)^c$ times the probability that the run following $p$ has not halted after $t$ random bits.

**Proof.** The nonhalting probability at time $t$ is exactly $2^{-t}$, by `notHaltedProb_rhoCoinRun`. Thus the sum in question is a partial sum of the nonnegative series with terms $(t+1)^c2^{-t}$. This series converges: the standard summability result for a polynomial times a geometric sequence applies because the ratio parameter $1/2$ has absolute value less than one. Choose a rational number $C$ strictly greater than the value of this real series. Every finite partial sum is at most the whole series, since its terms are nonnegative, and hence is at most $C$.

**Key facts.** `Randomized.notHaltedProb_rhoCoinRun`.
