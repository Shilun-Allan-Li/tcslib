<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.missProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Miss Probability Recurrence

**Claim.** After $k+1$ steps from $s$, the miss probability is $0$ if $s=t$; otherwise it is the average, over the neighbor slots of $s$, of the miss probability after $k$ steps from the resulting vertex.

**Proof.** The probability of hitting the target in the first step is $1$ if $s=t$, and otherwise is the average of the length-$k$ hit probabilities from the neighbors (`hitProb_succ`). Subtract this identity from $1$. In the case $s=t$, the miss probability is therefore zero. In the other case, distribute subtraction across the finite sum: each summand becomes one minus the corresponding hit probability, hence the length-$k$ miss probability at that neighbor. Dividing by the number $D$ of slots identifies the result as the stated average; the division is valid because $D>0$.

**Key facts.** `Randomized.RegularMultigraph.hitProb_succ`.
