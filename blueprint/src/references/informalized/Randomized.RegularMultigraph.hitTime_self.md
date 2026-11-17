<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Time at the Target

**Claim.** Starting from the target vertex, the truncated hitting time is zero for every horizon $N$.

**Proof.** By definition, the hitting time is a finite sum of miss probabilities, one for each $j<N$. The miss probability at the target is zero for every $j$ (`missProb_self`), so every summand vanishes and hence the sum is zero.

**Key facts.** `Randomized.RegularMultigraph.missProb_self`.
