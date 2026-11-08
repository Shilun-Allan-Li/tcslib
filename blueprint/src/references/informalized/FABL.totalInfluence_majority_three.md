<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.totalInfluence_majority_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Coordinate Majority Influence

**Claim.** The total influence of majority on three coordinates is $3/2$.

**Proof.** Apply the odd-majority influence formula with $m=1$: the total influence is $3\binom{2}{1}/2^2$. Since $\binom{2}{1}=2$, this simplifies to $3/2$.

**Key facts.** `FABL.totalInfluence_majority_odd`.
