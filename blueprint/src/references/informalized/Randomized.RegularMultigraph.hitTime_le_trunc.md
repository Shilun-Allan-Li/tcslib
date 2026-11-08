<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_trunc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncated Expected Hitting Time

**Claim.** For every integer $N\ge0$, the cumulative miss probability through step $N-1$ is at most $N$.

**Proof.** Each miss probability lies between zero and one, in particular it is at most one. Summing this bound over the $N$ indices from $0$ through $N-1$ gives a total at most $N$; when $N=0$, the sum is empty and equals zero.

**Key facts.** `Randomized.RegularMultigraph.missProb_mem_Icc`.
