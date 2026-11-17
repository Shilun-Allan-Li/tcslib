<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.totalInfluence_liftedOddMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of Lifted Odd Majority

**Claim.** For every natural number $m$, the total influence of odd majority on $2m+1$ coordinates equals the total influence of its lift to $2m+2$ coordinates that ignores the first coordinate.

**Proof.** Apply the decomposition of total influence by the first coordinate (`FABL.totalInfluence_cons`). The two restrictions obtained by fixing the first coordinate to $1$ or $-1$ are both the same odd-majority function on the remaining $2m+1$ coordinates, since the lifted function ignores the first coordinate. The remaining term in the decomposition is the probability that these two restrictions differ at a uniformly chosen input. They agree at every input, so this probability is zero. The average of the two equal restricted total influences is therefore exactly the total influence of odd majority on $2m+1$ coordinates.

**Key facts.** `FABL.totalInfluence_cons`.
