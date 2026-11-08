<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.majority_isOddFunc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of majority

**Claim.** Complementing every input bit of majority on $2m+1$ coordinates negates its value.

**Proof.** Let $A$ be the set of coordinates where $x_i$ is false. The coordinates where the complemented input is false are exactly the complement of $A$, so their number is $2m+1-|A|$. Also $|A|\le2m+1$. If $|A|>m$, then $2m+1-|A|\le m$, so the complemented input does not have a strict majority of false coordinates. If $|A|\le m$, then $2m+1-|A|>m$, so the complemented input does. In either case exactly one of the two inputs has majority value $1$, while the other has value $-1$, proving the claimed sign reversal.
