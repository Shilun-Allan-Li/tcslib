<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.one_sub_sqrt_le_of_hasSmallStableInfluences_leadingCoordinateTimes_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound for leading-coordinate majority

**Claim.** If every coordinate of the real-valued leading-coordinate majority on $2m+1$ signs has stable influence at parameter $1-\delta$ at most $\varepsilon$, where $0<\delta<1$, then $1-\sqrt\delta\le\varepsilon$.

**Proof.** The strict bounds on $\delta$ imply $\delta\in[0,1]$. The established lower bound for the stable influence of the leading-coordinate majority at coordinate $0$ (`one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd`) therefore gives $1-\sqrt\delta\le$ that influence. The small-influences hypothesis bounds the same coordinate's influence above by $\varepsilon$. Combining the two inequalities proves the claim.

**Key facts.** `FABL.one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd`.
